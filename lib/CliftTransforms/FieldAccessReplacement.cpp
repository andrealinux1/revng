//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <compare>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

#include "llvm/ADT/APInt.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Value.h"

#include "revng/Clift/Clift.h"
#include "revng/Clift/CliftEnums.h"
#include "revng/Clift/CliftTypes.h"
#include "revng/CliftTransforms/BestTraversal.h"
#include "revng/CliftTransforms/EmitFieldAccesses.h"
#include "revng/CliftTransforms/FieldAccessReplacement.h"
#include "revng/CliftTransforms/Passes.h"
#include "revng/CliftTransforms/PointerArithmetic.h"
#include "revng/Support/CTarget.h"

namespace clift = mlir::clift;
using namespace mlir::clift;

namespace {

// =============================================================================
// `Replacement` struct definition
// =============================================================================

/// `Replacement` is used as a builder class to perform the rewrite of the
/// pointer arithmetic with (multiple) `clift` `operation`s equivalent to the
/// elected `BestTraversal`
struct Replacement {

  /// `FieldAccessInfo` represent the atomic element of the `Replacement`. It
  /// can represent an access to `union`, `struct`, `array`, accompanied by the
  /// relative `Index`
  struct FieldAccessInfo {
    enum Kind {
      Union,
      Struct,
      Array
    } TheKind;

    // We need to have the possibility to represent and `Index` with both a
    // constant and a variable component (in order to represent access like
    // `[i + 4]`)
    std::pair<mlir::Value, uint64_t> Index;
  };

  /// We store the sequence of needed `FieldAccess`es here
  llvm::SmallVector<FieldAccessInfo> FieldAccesses;

  /// `LeftoverOffset` holds the eventual portion of the access that is not
  /// captured by the `BestTraversal`
  PointerArithmetic::OffsetExpression LeftoverOffset;

  /// This `static` method prepares the description of the `Replacement`, that
  /// will be later applied
  static Replacement make(const PointerArithmetic &Arithmetic,
                          const Traversal &BestTraversal);

  /// This method performs the actual `clift` IR rewriting,
  void replace(ExpressionOpInterface PointerToReplace,
               const PointerArithmetic &Arithmetic) const;
};

// =============================================================================
// `Replacement` methods implementation
// =============================================================================

/// Factory `make `constructor method
Replacement Replacement::make(const PointerArithmetic &Arithmetic,
                              const Traversal &BestTraversal) {

  auto BasePtrType = Arithmetic.BasePointer.getType().cast<PointerType>();
  auto BaseType = BasePtrType.getPointeeType();

  // Start with an empty `Replacement` object, which will be populated in this
  // routine
  Replacement Result;
  Result.LeftoverOffset.BaseOffset = llvm::APInt(64, 0);

  // Copy the starting `BestTraversal` and `Offset`, we will consume them in the
  // current phase

  // We initialize the `LeftoverTraversal` with the `BestTraversal` we
  // identified during phase 2, and we consume it until the whole `Replacement`
  // is produced
  Traversal LeftoverTraversal = BestTraversal;

  // We initialize the `LeftoverOffset` with the offset expression that was
  // produced in the `PointerArithmetic` during phase 1
  PointerArithmetic::OffsetExpression LeftoverOffset = Arithmetic.Offset;

  // We go over each component in the select `Traversal` and build the
  // `Replacement`
  while (LeftoverTraversal.TraversedFields.size() != 0
         or LeftoverTraversal.TraversedArrays.size() != 0) {

    // Inspect the `TypedefType` and cast to a known `clift` `Type`
    if (auto TypedefType = BaseType.dyn_cast<clift::TypedefType>()) {
      BaseType = TypedefType.getUnderlyingType().cast<mlir::Type>();
      continue;
    }

    // We should never reach these `Type`s by construction
    if (BaseType.isa<FunctionType>() or BaseType.isa<PointerType>()
        or BaseType.isa<PrimitiveType>() or BaseType.isa<EnumType>()) {
      revng_abort("Invalid type in traversal");
    }

    // Inspect the `struct`
    if (auto StructType = BaseType.dyn_cast<clift::StructType>()) {

      // We consume the traversed `struct`
      unsigned FieldIndex = LeftoverTraversal.TraversedFields.front();
      LeftoverTraversal.TraversedFields
        .erase(LeftoverTraversal.TraversedFields.begin());

      Result.FieldAccesses.push_back({ .TheKind = FieldAccessInfo::Struct,
                                       .Index = std::make_pair(mlir::Value(),
                                                               FieldIndex) });

      // Move to the field's type
      llvm::ArrayRef<FieldAttr> Fields = StructType.getFields();

      // Find field by offset
      unsigned Index = 0;
      bool Consumed = false;
      for (const FieldAttr &Field : Fields) {
        if (Index == FieldIndex) {
          BaseType = Field.getType().cast<mlir::Type>();
          Consumed = true;
          break;
        }

        // Subtract the size of the fields we traverse from the `LeftoverOffset`
        // `BaseOffset`, in order to take into account the portion of the
        // `LeftoverOffset` that we consume
        LeftoverOffset.BaseOffset -= Field.getType().getByteSize();

        Index++;
      }

      // We assert that at least one of the fields is consumed, meaning that we
      // found the field we were searching for
      revng_assert(Consumed);

      continue;
    }

    // Inspect the `union`
    if (auto UnionType = BaseType.dyn_cast<clift::UnionType>()) {

      // We don't need to subtract anything for a `Union`, cause all the fields
      // always start at 0
      unsigned FieldIndex = LeftoverTraversal.TraversedFields.front();
      LeftoverTraversal.TraversedFields
        .erase(LeftoverTraversal.TraversedFields.begin());

      Result.FieldAccesses.push_back({ .TheKind = FieldAccessInfo::Union,
                                       .Index = std::make_pair(mlir::Value(),
                                                               FieldIndex) });

      // Move to the field's type
      llvm::ArrayRef<FieldAttr> Fields = UnionType.getFields();

      // Find field by offset
      unsigned Index = 0;
      bool Consumed = false;
      for (const FieldAttr &Field : Fields) {
        if (Index == FieldIndex) {
          BaseType = Field.getType().cast<mlir::Type>();
          Consumed = true;
          break;
        }

        Index++;
      }

      // We assert that at least one of the fields is consumed, meaning that we
      // found the field we were searching for
      revng_assert(Consumed);

      continue;
    }

    // Inspect the `array`
    if (auto ArrayType = BaseType.dyn_cast<clift::ArrayType>()) {

      ArrayShape CurrentArray = *LeftoverTraversal.TraversedArrays.begin();
      LeftoverTraversal.TraversedArrays.erase(CurrentArray);

      // When reaching this iteration, if there was an array traversal in the
      // original traversal with a larger stride than the current, it must have
      // been already processed in a previous iteration
      if (not LeftoverOffset.LinearCombination.empty()) {
        revng_assert(LeftoverOffset.LinearCombination.front()
                       .Stride.ule(CurrentArray.Stride));
      }

      // We decide if we consume the offset from the `BaseOffset` or the
      // `LinearCombination`
      llvm::APInt NumFixedConsumedElements = llvm::APInt(64, 0);
      if (LeftoverOffset.BaseOffset.uge(CurrentArray.Stride)) {
        NumFixedConsumedElements = LeftoverOffset.BaseOffset
                                     .udiv(CurrentArray.Stride);
        LeftoverOffset.BaseOffset -= CurrentArray.Stride
                                     * NumFixedConsumedElements;
      }

      mlir::Value DynamicElementId = {};
      const auto &LinearCombination = LeftoverOffset.LinearCombination;
      if (not LinearCombination.empty()
          and LinearCombination.front().Stride == CurrentArray.Stride) {
        DynamicElementId = LeftoverOffset.LinearCombination.front().Index.first;
        LeftoverOffset.LinearCombination
          .erase(LeftoverOffset.LinearCombination.begin());
      }

      Result.FieldAccesses
        .push_back({ .TheKind = FieldAccessInfo::Array,
                     .Index = std::make_pair(DynamicElementId,
                                             NumFixedConsumedElements
                                               .getSExtValue()) });

      // Move to the `array` element `Type`
      BaseType = ArrayType.getElementType();

      continue;
    }
  }

  // We pass over the remaining `LeftoverOffset`
  Result.LeftoverOffset = LeftoverOffset;

  return Result;
}

void Replacement::replace(ExpressionOpInterface PointerToReplace,
                          const PointerArithmetic &Arithmetic) const {

  // TODO: We need the `PointerSize` in order to generate the `ImmediateOp`s
  //       used       to access the `struct` fields and `array` members, and to
  //       generate the `AddressOp` at the end of the field access substitution.
  //       We extract it from the `PointerToReplace` we are processing, since
  //       the information is not yet stored in the `mlir` module. In the
  //       future, if the `PointerSize` is encapsuled in the `mlir` module, we
  //       should use that source of information.
  auto PointerSize = PointerToReplace->getResult(0)
                       .getType()
                       .cast<PointerType>()
                       .getPointerSize();

  // Set insertion point right before the `PointerToReplace`
  mlir::OpBuilder Builder(PointerToReplace);
  mlir::Value CurrentValue = Arithmetic.BasePointer;

  // Every new `Operation` created in this phase will retain the `Location` of
  // the original `PointerToReplace`
  mlir::Location PointerToReplaceLoc = PointerToReplace.getLoc();

  // Apply each field access in sequence
  // Iterate over every `FieldAccess` in `Replacement`, and materialize the
  // `clift` `Operation`s needed to perform such access
  for (const FieldAccessInfo &Access : FieldAccesses) {
    switch (Access.TheKind) {
    case FieldAccessInfo::Kind::Struct: {
      auto Index = std::get<uint64_t>(Access.Index);
      StructType StructType;
      bool IsIndirectAccess = false;

      // We may need to unwrap the `StructType` from a `PointerType`
      if (isPointerType(CurrentValue.getType())) {
        auto StructPtrType = CurrentValue.getType().cast<PointerType>();
        StructType = StructPtrType.getPointeeType().cast<clift::StructType>();
        IsIndirectAccess = true;
      } else {
        StructType = CurrentValue.getType().cast<clift::StructType>();
        IsIndirectAccess = false;
      }

      // Emit the field access
      mlir::Type FieldType = StructType.getFields()[Index].getType();
      CurrentValue = Builder.create<AccessOp>(PointerToReplaceLoc,
                                              FieldType,
                                              CurrentValue,
                                              IsIndirectAccess,
                                              Index);
      break;
    }

    case FieldAccessInfo::Kind::Union: {
      auto Index = std::get<uint64_t>(Access.Index);
      UnionType UnionType;
      bool IsIndirectAccess = false;

      // We may need to unwrap the `UnionType` from a `PointerType`
      if (isPointerType(CurrentValue.getType())) {
        auto UnionPtrType = CurrentValue.getType().cast<PointerType>();
        UnionType = UnionPtrType.getPointeeType().cast<clift::UnionType>();
        IsIndirectAccess = true;
      } else {
        UnionType = CurrentValue.getType().cast<clift::UnionType>();
        IsIndirectAccess = false;
      }

      // Emit the field access
      mlir::Type FieldType = UnionType.getFields()[Index].getType();
      CurrentValue = Builder.create<AccessOp>(PointerToReplaceLoc,
                                              FieldType,
                                              CurrentValue,
                                              IsIndirectAccess,
                                              Index);
      break;
    }

    case FieldAccessInfo::Kind::Array: {

      // We may need to unwrap the `ArrayType` from a `PointerType`, and emit
      // the needed `IndirectionOp` and `Decay` cast accordingly
      ArrayType ArrayType;
      if (isPointerType(CurrentValue.getType())) {
        auto ArrayPtrType = CurrentValue.getType().cast<PointerType>();
        ArrayType = ArrayPtrType.getPointeeType().cast<clift::ArrayType>();

        // Add the indirection operation
        CurrentValue = Builder.create<IndirectionOp>(PointerToReplaceLoc,
                                                     CurrentValue);
      } else {
        ArrayType = CurrentValue.getType().cast<clift::ArrayType>();
      }

      // In this situation, we need to add a `decay` cast in order to be
      // able to perform the subscript access to the array
      auto ArrayElementType = ArrayType.getElementType();
      auto DecayType = PointerType::get(ArrayElementType, PointerSize);
      CurrentValue = Builder.create<CastOp>(PointerToReplaceLoc,
                                            DecayType,
                                            CurrentValue,
                                            CastKind::Decay);

      // Emit the `mlir::Value` representing the `Index` access.
      // We declare all the possible components (constant and variable parts) as
      // uninitialized here, and later fill only the components that we need to
      // emit.
      mlir::Value FixedIndexValue = {};
      mlir::Value DynamicIndexValue = {};
      mlir::Value IndexValue = {};

      // If present, we emit a new `mlir::Value` representing the constant
      // component of the `Index` access
      if (Access.Index.second != 0) {
        auto Index = Access.Index.second;
        auto IntegerType = PrimitiveType::get(Builder.getContext(),
                                              PrimitiveKind::GenericKind,
                                              PointerSize);
        FixedIndexValue = Builder.create<ImmediateOp>(PointerToReplaceLoc,
                                                      IntegerType,
                                                      Index);
      }

      // If present, we emit a new `mlir::Value` representing the variable
      // component of the `Index` access
      if (Access.Index.first) {
        DynamicIndexValue = std::get<mlir::Value>(Access.Index);
      }

      // We compose the constant and variable components of the `Index` access
      // depending on whether they are present
      if (FixedIndexValue and DynamicIndexValue) {
        IndexValue = Builder.create<AddOp>(PointerToReplaceLoc,
                                           FixedIndexValue,
                                           DynamicIndexValue);
      } else if (FixedIndexValue) {
        IndexValue = FixedIndexValue;
      } else {
        IndexValue = DynamicIndexValue;
      }

      // Finally, we emit the `SubscriptOp` using as `Index` the `mlir::Value`
      // constructed above
      CurrentValue = Builder.create<SubscriptOp>(PointerToReplaceLoc,
                                                 CurrentValue,
                                                 IndexValue);

      break;
    }
    }
  }

  // Take address of the result, since we always start the replacement from a
  // `PointerType`, we want to get back to it
  auto CurrentValuePointerType = PointerType::get(CurrentValue.getType(),
                                                  PointerSize);
  CurrentValue = Builder.create<AddressofOp>(PointerToReplaceLoc,
                                             CurrentValuePointerType,
                                             CurrentValue);

  // If there is a non-null `LeftoverOffset`, we add it as integer arithmetic
  if (not LeftoverOffset.BaseOffset.isZero()
      or not LeftoverOffset.LinearCombination.empty()) {

    // Cast pointer to integer
    auto IntegerType = PrimitiveType::get(Builder.getContext(),
                                          PrimitiveKind::GenericKind,
                                          PointerSize);
    CurrentValue = Builder.create<CastOp>(PointerToReplaceLoc,
                                          IntegerType,
                                          CurrentValue,
                                          CastKind::Bitcast);

    // Add base offset
    if (!LeftoverOffset.BaseOffset.isZero()) {
      auto IntegerType = PrimitiveType::get(Builder.getContext(),
                                            PrimitiveKind::GenericKind,
                                            PointerSize);

      auto LeftoverOffsetValue = LeftoverOffset.BaseOffset.getSExtValue();
      auto AddOperandValue = Builder.create<ImmediateOp>(PointerToReplaceLoc,
                                                         IntegerType,
                                                         LeftoverOffsetValue);
      CurrentValue = Builder.create<AddOp>(PointerToReplaceLoc,
                                           CurrentValue,
                                           AddOperandValue);
    }

    // Add strided terms
    for (const auto &Term : LeftoverOffset.LinearCombination) {
      // Multiply stride by index
      auto IndexValue = Builder.create<ImmediateOp>(PointerToReplaceLoc,
                                                    IntegerType,
                                                    Term.Index.second
                                                      .getSExtValue());
      auto StrideValue = Builder
                           .create<ImmediateOp>(PointerToReplaceLoc,
                                                IntegerType,
                                                Term.Stride.getSExtValue());
      auto StridedValue = Builder.create<clift::MulOp>(PointerToReplaceLoc,
                                                       IndexValue,
                                                       StrideValue);
      CurrentValue = Builder.create<clift::AddOp>(PointerToReplaceLoc,
                                                  CurrentValue,
                                                  StridedValue);
    }

    // Cast back to pointer
    auto PointerType = PointerType::get(CurrentValue.getType(), PointerSize);
    CurrentValue = Builder.create<CastOp>(PointerToReplaceLoc,
                                          PointerType,
                                          CurrentValue,
                                          CastKind::Bitcast);
  }

  // If the result type differs from PointerToReplace's type, add a cast on
  // `clift` IR in order to make the replacement fit the replaced
  // `PointerToReplace` `Type`
  auto PointerToReplaceOp = PointerToReplace.getOperation();
  if (CurrentValue.getType() != PointerToReplace->getResult(0).getType()) {
    CurrentValue = Builder
                     .create<CastOp>(PointerToReplaceLoc,
                                     PointerToReplace->getResult(0).getType(),
                                     CurrentValue,
                                     CastKind::Bitcast);
  }

  // Replace all uses of `PointerToReplace` with `CurrentValue`
  if (CurrentValue != Arithmetic.BasePointer) {
    PointerToReplace->getResult(0).replaceAllUsesWith(CurrentValue);
  }

  // At this point, we are left in the `clift` IR with a set of dead `Value`s
  // representing the old `PointerArithmetic`. We rely on a subsequent DCE pass
  // to clean up all the dead `Value`s.
}
} // namespace

/// Entry point function to perform the replacement of the pointer arithmetic
/// access (`PointerToReplace`), with operations equivalent to the
/// `BestTraversal` elected in the previous steps
void replaceFieldAccess(ExpressionOpInterface PointerToReplace,
                        const PointerArithmetic &Arithmetic,
                        const Traversal &BestTraversal) {

  // We prepare the `Replacement`, which describes the `Traversal` in a way that
  // can easily be converted into a series of `clift` `operation`s
  auto R = Replacement::make(Arithmetic, BestTraversal);

  // We actually perform the replacement
  R.replace(PointerToReplace, Arithmetic);
}
