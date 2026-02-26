//
// This file is distributed under the MIT License. See LICENSE.md for details.
//
#include <compare>
#include <cstdint>
#include <memory>
#include <optional>

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"

#include "revng/Clift/Clift.h"
#include "revng/Clift/CliftEnums.h"
#include "revng/Clift/CliftOpInterfaces.h"
#include "EmitFieldAccesses.h"
#include "revng/CliftTransforms/Passes.h"
#include "PointerArithmetic.h"
#include "revng/Support/CTarget.h"

namespace clift = mlir::clift;
using namespace clift;

static Logger Log("pointer-arithmetic");

// =============================================================================
// `PointerArithmetic` class methods
// =============================================================================

PointerArithmetic::OffsetExpression::OffsetExpression() : BaseOffset(64, 0) {
}

PointerArithmetic::OffsetExpression::OffsetExpression(llvm::APInt Offset) :
  BaseOffset(Offset) {
}

bool PointerArithmetic::isNumeric() const {
  return !BasePointer;
}

bool PointerArithmetic::isAddress() const {
  return !!BasePointer;
}

bool PointerArithmetic::verify() const {

  const auto &LinearCombination = Offset.LinearCombination;

  // Check that strides are strictly positive. Negative or null strides do not
  // make sense
  for (const auto &Term : LinearCombination) {
    if (Term.Stride.isNegative() or Term.Stride.isZero()) {
      return false;
    }
  }

  // Check that we do not have duplicated strides, and that they are in
  // descending order
  for (size_t I = 0; I < LinearCombination.size(); I++) {
    for (size_t J = I + 1; J < LinearCombination.size(); J++) {
      if (LinearCombination[I].Stride == LinearCombination[J].Stride) {
        return false;
      }
      if (LinearCombination[I].Stride.ult(LinearCombination[J].Stride)) {
        return false;
      }
    }
  }

  // If we pass all the previous checks, we have a valid `PointerArithmetic`
  return true;
}

void PointerArithmetic::dump() const {

  Log << "Dumping PointerArithmetic object:\n";

  Log << "  BasePointer: ";
  if (BasePointer) {
    mlir::Value ValueToPrint = BasePointer;
    ValueToPrint.print(*Log.getAsLLVMStream());
    Log << "\n";
  } else {
    Log << "(null)\n";
  }

  Log << "  Base Offset: ";
  Log << Offset.BaseOffset.getSExtValue() << "\n";

  Log << "  Linear Combinations (" << Offset.LinearCombination.size()
      << " terms):\n";

  for (size_t I = 0; I < Offset.LinearCombination.size(); ++I) {
    const auto &Combination = Offset.LinearCombination[I];
    Log << "    Term #" << I << ":\n";
    Log << "      Stride: ";
    Log << Combination.Stride.getZExtValue() << "\n";

    Log << "      Dynamic Index: ";
    if (Combination.Idx.Variable) {
      mlir::Value ValueToPrint = Combination.Idx.Variable;
      ValueToPrint.print(*Log.getAsLLVMStream());
    } else {
      Log << "(null)";
    }
    Log << "\n";

    Log << "      Fixed Offset: ";
    Log << Combination.Idx.Constant.getSExtValue() << ")\n";
  }

  Log << "\n";
  Log.flush();
}

namespace {

// =============================================================================
// `PointerArithmeticImpl` class implementation, which contains the logic used
// to compute the resulting `PointerArithmetic`
// =============================================================================

/// The `PointerArithmeticImpl` class is the main helper class used for
/// computing the `PointerArithmetic` object starting from the
/// `PointerToReplace`
class PointerArithmeticImpl {
public:
  PointerArithmeticImpl() = default;

  // Compute pointer arithmetic for a given `PointerToReplace`
  std::optional<PointerArithmetic>
  computePointerArithmetic(mlir::clift::ExpressionOpInterface PointerToReplace);

private:
  // Traversal function to inspect the operands
  std::optional<PointerArithmetic> traverse(mlir::Value V);

  // Return the `PointerArithmetic` for the leaf nodes
  PointerArithmetic createLeafPA(mlir::Value V);

  // Methods which are used to compose the currently computed
  // `PointerArithmetic` with different `clift` `Operation`s that want to
  // traverse during our exploration
  std::optional<PointerArithmetic> composeBitcast(CastOp Bitcast);

  std::optional<PointerArithmetic> composeAdd(AddOp Add);

  std::optional<PointerArithmetic> composePtrAdd(PtrAddOp PtrAdd);

  std::optional<PointerArithmetic> composeMul(MulOp Mul);

  std::optional<PointerArithmetic> composeShl(ShiftLeftOp ShiftLeft);

  // Contains the logic to merge two `PointerArithmetic` objects
  std::optional<PointerArithmetic>
  mergeArithmetics(const PointerArithmetic &LHS, const PointerArithmetic &RHS);

  // Helper function used to multiply all the `PointerArithmetic` strides and
  // offset by a constant
  PointerArithmetic multiplyByConstant(PointerArithmetic &PA,
                                       const llvm::APInt &Multiplier);

  // Helper function used to sort linear combination by stride, in descending
  // order
  void sortLinearCombination(PointerArithmetic &PA);
};

// =============================================================================
// Static helper standalone functions
// =============================================================================

/// Helper function used to check if the `Value` is a `PointerType`
static bool isPointerType(mlir::Value V) {

  // If we are in presence of an `ExpressionOp` of pointer type, we return true
  if (auto Addressof = mlir::dyn_cast_or_null<AddressofOp>(V.getDefiningOp())) {
    return true;
  }

  return false;
}

/// Helper function used to verify if an `ExpressionOpInterface` is
/// `PointerType`d
static bool isPointerTypeExpr(ExpressionOpInterface Expr) {
  // We verify that the expression produces a result
  if (not Expr->getResult(0)) {
    return false;
  }
  if (not Expr->getResult(0).getType()) {
    return false;
  }
  if (not Expr->getResult(0).getType().isa<PointerType>()) {
    return false;
  }

  return true;
}

/// Helper function used to extract the underlying constant value from an
/// `Value`
std::optional<llvm::APInt> getConstantValue(mlir::Value V) {
  if (auto Immediate = llvm::dyn_cast_or_null<ImmediateOp>(V.getDefiningOp())) {
    return llvm::APInt(64, Immediate.getValue());
  }

  return std::nullopt;
}

// =============================================================================
// `PointerArithmeticImpl` class methods
// =============================================================================

std::optional<PointerArithmetic>
PointerArithmeticImpl::computePointerArithmetic(ExpressionOpInterface
                                                  PointerToReplace) {

  // We skip every non pointer-typed `PointerToReplace`
  if (not isPointerTypeExpr(PointerToReplace)) {
    return std::nullopt;
  }

  // We traverse upwards the dataflow starting from the
  auto Result = traverse(PointerToReplace->getResult(0));

  // If we got a numeric result, discard it, since we cannot use it
  if (Result && Result->isNumeric()) {
    return std::nullopt;
  }

  // Verify invariants for the obtained `PointerArithmetic`
  if (Result && !Result->verify()) {
    return std::nullopt;
  }

  // Log the resulting `PointerArithmetic`, together with the initial
  // `PointerToReplace` it was produced from
  if (Log.isEnabled() and PointerToReplace and Result) {
    Log << "PointerArithmetic Relative to operation:\n";
    PointerToReplace.print(*Log.getAsLLVMStream());
    Log << "\n";
    Result->dump();
  }

  // If we reach this point, it means that we successfully computed the
  // `PointerArithmetic` object, so we can return it, so that the rewrite can
  // happen in later phases
  return Result;
}

std::optional<PointerArithmetic>
PointerArithmeticImpl::traverse(mlir::Value V) {

  // Every time we find a compatible `Expression`, we traverse it in order to
  // compose its operands
  auto VOp = V.getDefiningOp();
  if (auto Expr = mlir::dyn_cast_or_null<ExpressionOpInterface>(VOp)) {
    if (auto Cast = mlir::dyn_cast<CastOp>(Expr.getOperation())) {
      if (Cast.getKind() == CastKind::Bitcast) {
        return composeBitcast(Cast);
      }
    } else if (auto Add = mlir::dyn_cast<AddOp>(Expr.getOperation())) {
      return composeAdd(Add);
    } else if (auto PtrAdd = mlir::dyn_cast<PtrAddOp>(Expr.getOperation())) {
      return composePtrAdd(PtrAdd);
    } else if (auto Mul = mlir::dyn_cast<MulOp>(Expr.getOperation())) {
      return composeMul(Mul);
    } else if (auto
                 ShiftLeft = mlir::dyn_cast<ShiftLeftOp>(Expr.getOperation())) {
      return composeShl(ShiftLeft);
    }
  }

  // If we do not traverse V, we create the leaf
  return createLeafPA(V);
}

PointerArithmetic PointerArithmeticImpl::createLeafPA(mlir::Value V) {
  PointerArithmetic PA;
  auto VOp = V.getDefiningOp();

  if (isPointerType(V)) {

    // Pointer typed expression
    PA.BasePointer = V;
    PA.Offset = PointerArithmetic::OffsetExpression(llvm::APInt(64, 0));
  } else if (auto ConstantValue = getConstantValue(V)) {

    // Integer Constant
    PA.Offset = PointerArithmetic::OffsetExpression(*ConstantValue);
  } else {

    // We want to handle `ExpressionOpInterface`s and `mlir::BlockArgument`s for
    // building leaf `PA` containing a `LinearCombination`. These can be the
    // `Index` component of an array access.
    if ((VOp and (isa<ExpressionOpInterface>(VOp)))
        or isa<mlir::BlockArgument>(V)) {

      // Generic offset expression - strided 1 term
      PA.Offset = PointerArithmetic::OffsetExpression(llvm::APInt(64, 0));
      PA.Offset.LinearCombination.emplace_back(
        llvm::APInt(64, 1),
        PointerArithmetic::Index{ V, llvm::APInt(64, 0) });
    }
  }

  return PA;
}

std::optional<PointerArithmetic>
PointerArithmeticImpl::composeBitcast(CastOp Cast) {

  // Retrieve the `bitcast` single `Operand`, and recursively forward the
  // `PointerArithmetic` produced from it
  auto Operand = Cast->getOperand(0);
  return traverse(Operand);
}

std::optional<PointerArithmetic> PointerArithmeticImpl::composeAdd(AddOp Add) {
  auto LHS = Add->getOperand(0);
  auto RHS = Add->getOperand(1);

  auto LHSPA = traverse(LHS);
  auto RHSPA = traverse(RHS);

  // It may happen that either the LHS or the RHS traversal produced an invalid
  // `PointerArithmetic` result. In such case, we need to propagate upward the
  // failure.
  if (not LHSPA or not RHSPA) {
    return std::nullopt;
  }

  // It may happen that both `LHSPA` or `RHSPA` have an address
  // `PointerArithmetic`. In such situation, we cannot know which one is the
  // `BasePointer`, so we bail out from the construction of the
  // `PointerArithmetic` result.
  if (LHSPA->isAddress() and RHSPA->isAddress()) {
    return std::nullopt;
  }

  // If we have valid `PointerArithmetics` for both the operands, we compose the
  // results and propagate them upwards
  return mergeArithmetics(*LHSPA, *RHSPA);
}

std::optional<PointerArithmetic>
PointerArithmeticImpl::composePtrAdd(PtrAddOp Add) {

  mlir::Value PointerOperand = Add.getPointer();
  mlir::Value OffsetOperand = Add.getOffset();

  // Compute the `PointerArithmetic` for both the pointer and offset operands.
  auto PointerOperandPA = traverse(PointerOperand);
  auto OffsetOperandPA = traverse(OffsetOperand);

  // We should check that the pointer and offset operands are not both `numeric`
  // or `address`
  revng_assert(not(PointerOperandPA->isAddress()
                   and OffsetOperandPA->isAddress()));
  revng_assert(not(PointerOperandPA->isNumeric()
                   and OffsetOperandPA->isAddress()));

  // We expect that the offset operand is indeed a numeric `PointerArithmetic`.
  // We need this so that we can multiply the size of the clift pointee type by
  // the value that the numeric `PointerArithmetic` brings with it.
  revng_assert(OffsetOperandPA->isNumeric());

  // We multiply the size of the `PointerOperand` operand by the `OffsetOperand`
  // `BaseOffset`. The multiplication factor is contained into the `BaseOffset`
  // of the numeric operand.
  auto PointerOperandType = mlir::cast<PointerType>(PointerOperand.getType());
  auto PointerOperandTypeSize = PointerOperandType.getPointerSize();
  PointerOperandPA->Offset.BaseOffset += OffsetOperandPA->Offset.BaseOffset
                                         * PointerOperandTypeSize;

  return PointerOperandPA;
}

std::optional<PointerArithmetic> PointerArithmeticImpl::composeMul(MulOp Mul) {
  auto LHS = Mul.getOperand(0);
  auto RHS = Mul.getOperand(1);

  // Categorize the `Mul` operands constant and non constant, so that we can
  // choose which one to traverse
  std::optional<llvm::APInt> Constant;
  mlir::Value Variable;

  if (auto C = getConstantValue(LHS)) {
    Constant = C;
    Variable = RHS;
  } else if (auto C = getConstantValue(RHS)) {
    Constant = C;
    Variable = LHS;
  } else {

    // Neither operand is constant, this should not happen
    revng_abort();
  }

  // Traverse the variable operand
  auto VarPA = traverse(Variable);
  if (not VarPA) {
    return std::nullopt;
  }

  // Multiply the result and make it numeric
  auto Result = multiplyByConstant(*VarPA, *Constant);
  Result.BasePointer = mlir::Value();

  return Result;
}

std::optional<PointerArithmetic>
PointerArithmeticImpl::composeShl(ShiftLeftOp Shl) {

  // Handling is similar to `MulOp`, shift by N is multiplication by 2^N
  auto LHS = Shl.getOperand(0);
  auto RHS = Shl.getOperand(1);

  auto ShiftAmount = getConstantValue(RHS);

  // We do not have a constant amount to perform the shift, so we bail out
  if (not ShiftAmount) {
    return std::nullopt;
  }

  // We craft multiplication factor equivalent to the shift amount
  llvm::APInt Multiplier = llvm::APInt(64, 1).shl(*ShiftAmount);

  // We traverse the variable operand
  auto LHSPA = traverse(LHS);
  if (not LHSPA) {
    return std::nullopt;
  }

  // Multiply the result and make it numeric
  auto Result = multiplyByConstant(*LHSPA, Multiplier);
  Result.BasePointer = mlir::Value();

  return Result;
}

std::optional<PointerArithmetic>
PointerArithmeticImpl::mergeArithmetics(const PointerArithmetic &LHS,
                                        const PointerArithmetic &RHS) {

  PointerArithmetic Result;

  // Add the `BaseOffsets`
  Result.Offset.BaseOffset = LHS.Offset.BaseOffset + RHS.Offset.BaseOffset;

  // Append the linear combinations of `LHS` and `RHS`
  Result.Offset.LinearCombination = LHS.Offset.LinearCombination;
  Result.Offset.LinearCombination.append(RHS.Offset.LinearCombination.begin(),
                                         RHS.Offset.LinearCombination.end());

  // After we combined the `LinearCombination`s coming from the operands, we
  // sort them in descending order so that larger `Stride`s come before shorter
  // ones. This is the expected form derived from a nested array access, where
  // the stride of the _outer_ level is greater than the _inner_ one by
  // construction. Duplicate strides are checked in the verify phase as an
  // invariant.
  sortLinearCombination(Result);

  // Set the base pointer to either the `LHS` or `RHS`
  // At this point, we cannot have that both the operands are of address type
  revng_assert(not(LHS.isAddress() and RHS.isAddress()));

  // We propagate as the `BasePointer` of the result the one corresponding to
  // the _address_ part of the traversal
  if (LHS.isAddress()) {
    Result.BasePointer = LHS.BasePointer;
  } else if (RHS.isAddress()) {
    Result.BasePointer = RHS.BasePointer;
  }

  return Result;
}

PointerArithmetic
PointerArithmeticImpl::multiplyByConstant(PointerArithmetic &PA,
                                          const llvm::APInt &Multiplier) {

  // Multiply the base offset
  PA.Offset.BaseOffset = PA.Offset.BaseOffset * Multiplier;

  // Multiply all the strides contained in the `LinearCombination`s
  for (auto &Term : PA.Offset.LinearCombination) {
    Term.Stride = Term.Stride * Multiplier;
  }

  return PA;
}

void PointerArithmeticImpl::sortLinearCombination(PointerArithmetic &PA) {
  std::sort(PA.Offset.LinearCombination.begin(),
            PA.Offset.LinearCombination.end(),
            [](const auto &First, const auto &Second) {
              return First.Stride.ugt(Second.Stride);
            });
}

} // namespace

std::optional<PointerArithmetic>
computePointerArithmetic(mlir::clift::ExpressionOpInterface PointerToReplace) {
  auto Impl = PointerArithmeticImpl();
  return Impl.computePointerArithmetic(PointerToReplace);
}
