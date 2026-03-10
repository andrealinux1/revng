//
// This file is distributed under the MIT License. See LICENSE.md for details.
//
#include <compare>
#include <optional>
#include <set>

#include "revng/ADT/RecursiveCoroutine.h"
#include "revng/Clift/Clift.h"
#include "revng/Support/Assert.h"

#include "BestTraversal.h"
#include "PointerArithmetic.h"

namespace clift = mlir::clift;
using namespace clift;

static Logger Log("best-traversal");

/// Helper function used to retrieve the byte size of any `mlir::Type`
static uint64_t getTypeSize(mlir::Type Type) {
  return mlir::cast<clift::ValueType>(Type).getByteSize();
}

// =============================================================================
// `ArrayShape` class methods
// =============================================================================

bool ArrayShape::operator<(const ArrayShape &Other) const {
  if (Stride != Other.Stride) {

    // Larger strides are organized first
    return Stride > Other.Stride;
  }
  return NumElements < Other.NumElements;
}

// =============================================================================
// `Traversal` class methods
// =============================================================================

long Traversal::depth() const {
  return TraversedArrays.size() + TraversedFields.size();
}

int64_t Traversal::begin() const {
  return StartOffset + LeftoverOffset;
}

int64_t Traversal::end() const {
  return begin() + getTypeSize(TargetType);
}

bool Traversal::isShallow() const {
  return TraversedFields.empty() and TraversedArrays.empty();
}

void Traversal::dump() const {

  Log << "\nDumping Traversal:\n";

  // We dump the `TargetType` on which the `Traversal` lands on
  Log << "  TargetType: ";
  TargetType.print(*Log.getAsLLVMStream());
  Log << "\n";

  // Dump the `StartOffset` and `LeftoverOffset`
  Log << "  StartOffset: " << StartOffset << "\n";
  Log << "  LeftoverOffset: " << LeftoverOffset << "\n";

  // Dump all the `Traversed Fields` which this `Traversal` describes
  Log << "  Traversed Fields (" << TraversedFields.size() << "): [";
  for (size_t I = 0; I < TraversedFields.size(); ++I) {
    if (I > 0)
      Log << ", ";
    Log << TraversedFields[I];
  }
  Log << "]\n";

  // Dump all the `TraversedArray` which this `Traversal` describes
  Log << "  Traversed Arrays (" << TraversedArrays.size() << "):\n";
  for (const auto &Array : TraversedArrays) {
    Log << "    { NumElements: " << Array.NumElements
        << ", Stride: " << Array.Stride << " }\n";
  }

  Log << "\n";
  Log.flush();
}

namespace {

// =============================================================================
// Static helper functions
// =============================================================================

/// Helper function which converts a generic `ArrayPath` to a compatible form
/// used to store the `array` traversal into the `Traversal` class. The
/// re-ordering in descending `Stride` order is provided by the comparison
/// operator of `ArrayShape`
static llvm::SmallVector<ArrayShape>
arrayPathToSortedVector(const ArrayPath &Path) {
  llvm::SmallVector<ArrayShape> Result;
  Result.reserve(Path.size());
  for (const NestedArrayShape &Nested : Path) {
    ArrayShape Shape;
    Shape.NumElements = Nested.NumElements;
    Shape.Stride = Nested.Stride;
    Result.push_back(Shape);
  }
  llvm::sort(Result);
  return Result;
}

/// Helper function which checks if the `BaseOffset` falls inside of the
/// innermost `array` described by the `ArrayPath`
static bool isCompatible(const ArrayPath &Path, llvm::APInt BaseOffset) {
  for (const NestedArrayShape &Shape : Path) {

    // If the offset doesn't reach the offset of this `Shape` inside its parent
    // we just bail out
    if (BaseOffset.ult(Shape.OffsetFromParentArrayElement)) {
      return false;
    }

    BaseOffset -= Shape.OffsetFromParentArrayElement;

    // If we're entering in an array element past the first, we have to adjust
    // `BaseOffset`, consuming it
    if (BaseOffset.uge(Shape.Stride)) {

      // If we're jumping over the whole array, past it, we just bail out
      if (BaseOffset.uge(Shape.Stride * Shape.NumElements)) {
        return false;
      }

      // Otherwise adjust the `BaseOffset`, to set it to the offset inside the
      // array element we're traversing
      BaseOffset = BaseOffset.urem(Shape.Stride);
    }
  }

  // If we reach this point, it means that the `ArrayPath` was inedeed
  // compatible
  return true;
}

/// Helper function which finds all the `ArrayPath`s that are compatible with a
/// given `BaseOffset`
static llvm::SmallVector<const ArrayPath *>
findCompatibleArrayPaths(const std::vector<ArrayPath> &AllArrayPaths,
                         const llvm::APInt &BaseOffset) {
  llvm::SmallVector<const ArrayPath *> CompatibleArrays;
  for (const ArrayPath &Path : AllArrayPaths) {
    if (isCompatible(Path, BaseOffset))
      CompatibleArrays.push_back(&Path);
  }
  return CompatibleArrays;
}

/// Helper function which counts the length of the common prefix between two
/// sorted `TraversedArrays` vectors. Since both are sorted in descending stride
/// order, this counts how many leading array shapes match exactly.
static int64_t commonPrefixStrides(const llvm::ArrayRef<ArrayShape> &LHS,
                                   const llvm::ArrayRef<ArrayShape> &RHS) {
  int64_t Count = 0;
  auto LIt = LHS.begin();
  auto RIt = RHS.begin();

  while (LIt != LHS.end() && RIt != RHS.end() && *LIt == *RIt) {
    ++Count;
    ++LIt;
    ++RIt;
  }

  return Count;
}

// =============================================================================
// `TypeDistance` helper methods definition
// =============================================================================

/// The `TypeDistanceLatticeCompute` class is an helper class that computes the
/// `TypeDistance` if we need to resort to the lattice usage.
/// The criterion is described by the following lattice:
/// enum1 enum2
///  \    |
/// unsigned   signed
///        \   /
///        number  pointer_to_A  pointer_to_B
///            \   /           /
///           pointer_or_number   float
///                       \      /
///                        generic
///
/// TODO: this distance is NOT symmetric. It counts only upward steps from
///       Explicit to the least common ancestor (LCA) of Explicit and Ideal. For
///       example, typeDistance(unsigned, number) = 1, but typeDistance(number,
///       unsigned) = 0. Double check that this is the wanted behavior.
// Whenever we have to walk upwards, we weight each step upward 1.
class TypeDistanceLatticeCompute {

  // Define lattice node types for classification
  enum class LatticeNode {
    Enum,
    Unsigned,
    Signed,
    Float,
    Pointer,
    Number,
    PointerOrNumber,
    Generic
  };

private:
  // Helper function to classify a `Type` into its `LatticeNode`
  LatticeNode classifyType(mlir::Type T) {
    if (auto PType = T.dyn_cast<PrimitiveType>()) {
      auto Kind = PType.getKind();

      // Assign the `PrimitiveKind`s
      if (Kind == PrimitiveKind::GenericKind) {
        return LatticeNode::Generic;
      } else if (Kind == PrimitiveKind::PointerOrNumberKind) {
        return LatticeNode::PointerOrNumber;
      } else if (Kind == PrimitiveKind::NumberKind) {
        return LatticeNode::Number;
      } else if (Kind == PrimitiveKind::UnsignedKind) {
        return LatticeNode::Unsigned;
      } else if (Kind == PrimitiveKind::SignedKind) {
        return LatticeNode::Signed;
      } else if (Kind == PrimitiveKind::FloatKind) {
        return LatticeNode::Float;
      }
    }

    if (T.isa<EnumType>()) {
      return LatticeNode::Enum;
    }

    if (T.isa<PointerType>()) {
      return LatticeNode::Pointer;
    }

    // Shouldn't reach here given earlier checks
    revng_abort("We cannot identify suitable `LatticeNode` for `Type` `T`");
  };

  // Helper function to get the distance to a common ancestor
  uint64_t getDistanceToNode(LatticeNode From, LatticeNode To) {
    auto Ancestors = getAncestors(From);

    // We walk up the list of ancenstors counting the steps
    for (auto [I, Ancestor] : llvm::enumerate(Ancestors)) {
      if (Ancestor == To)
        return I;
    }

    // In case we found no path from `From` to `To` we return a placeholder
    // value
    return std::numeric_limits<uint64_t>::max();
  }

  // Helper method which returns the ordered list of `Ancestor`s of a
  // `LatticeNode`
  std::vector<LatticeNode> getAncestors(LatticeNode N) {
    using LN = LatticeNode;
    switch (N) {
    case LN::Enum:
      return {
        LN::Enum, LN::Unsigned, LN::Number, LN::PointerOrNumber, LN::Generic
      };
    case LN::Unsigned:
      return { LN::Unsigned, LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::Signed:
      return { LN::Signed, LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::Number:
      return { LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::Pointer:
      return { LN::Pointer, LN::PointerOrNumber, LN::Generic };
    case LN::PointerOrNumber:
      return { LN::PointerOrNumber, LN::Generic };
    case LN::Float:
      return { LN::Float, LN::Generic };
    case LN::Generic:
      return { LN::Generic };
    }
    revng_abort("Unhandled LatticeNode");
  }

  // Helper to find least common ancestor (LCA) in the lattice
  LatticeNode findLCA(LatticeNode A, LatticeNode B) {

    // At this point, `A == B` can only be only in case we have `Enum`
    // or `Pointer` (because they are two distinct type of the same
    // family). Identical primitive type are caught by the `LHS == RHS` early
    // exit check in `typeDistance`.
    if (A == B) {
      revng_assert(A == LatticeNode::Enum or A == LatticeNode::Pointer);
    }

    // For each node, its ordered ancestor chain from self to `Generic`
    // (inclusive). Enum/Pointer represent *families* of
    // distinct types, so when A == B for these, the LCA is their parent
    // (handled via SameFamily). The
    auto AncestorsA = getAncestors(A);
    auto AncestorsB = getAncestors(B);
    std::set<LatticeNode> SetB(AncestorsB.begin(), AncestorsB.end());

    // When A == B, it can only be `Enum` or `Pointer`.
    // In that case, skip self and start from the parent.
    size_t StartIdx = (A == B) ? 1 : 0;
    for (size_t I = StartIdx; I < AncestorsA.size(); ++I) {
      auto AncestorI = AncestorsA.at(I);

      // As soon as we reach an ancestor in common, we found the `LCA`
      if (SetB.count(AncestorI))
        return AncestorI;
    }

    revng_abort("LCA not found, `Generic` should always be a common ancestor");
  }

public:
  uint64_t getTypeDistance(mlir::Type Explicit, mlir::Type Ideal) {

    // Classify both types
    LatticeNode ExplicitNode = classifyType(Explicit);
    LatticeNode IdealNode = classifyType(Ideal);

    // Find their least common ancestor (LCA)
    LatticeNode LCA = findLCA(ExplicitNode, IdealNode);

    // Distance is defined as the number of upward steps from `ExplicitNode` to
    // LCA
    uint64_t Distance = getDistanceToNode(ExplicitNode, LCA);

    return Distance;
  }
};

/// The `typeDistance` function is a helper function which computes the defined
/// `TypeDistance`, according to the following criteria:
/// If the sizes of the input types differ, this distance is just "infinity". If
/// the inputs are not scalar, this distance is also "infinity". If they're both
/// scalars we should use the lattice approach, based on the primitives but
/// extended with enums and pointers. `Typedef`s are ignored. In such case, we
/// employ the `TypeDistanceLatticeCompute` helper class to perform the
/// computation.
static uint64_t typeDistance(mlir::Type Explicit, mlir::Type Ideal) {

  // First, unwrap any typedefs as they should be traversed in order to reach
  // the underlying type
  while (auto TypedefExplicit = Explicit.dyn_cast<TypedefType>()) {
    Explicit = TypedefExplicit.getUnderlyingType().cast<mlir::Type>();
  }
  while (auto TypedefIdeal = Ideal.dyn_cast<TypedefType>()) {
    Ideal = TypedefIdeal.getUnderlyingType().cast<mlir::Type>();
  }

  // If sizes differ, the `TypeDistance` is infinity
  if (getTypeSize(Explicit) != getTypeSize(Ideal)) {
    return std::numeric_limits<uint64_t>::max();
  }

  // If only one is _scalar_, the distance is defined as infinity
  if (!isScalarType(Explicit) || !isScalarType(Ideal)) {
    return std::numeric_limits<uint64_t>::max();
  }

  // If they're exactly the same type, `TypeDistance` is 0
  if (Explicit == Ideal) {
    return 0;
  }

  // In all the other cases, we compute the `TypeDistance` using an ad-hoc
  // lattice
  TypeDistanceLatticeCompute TDC;
  return TDC.getTypeDistance(Explicit, Ideal);
}

// =============================================================================
// `Score` class definition
// =============================================================================

/// We represent the `SizeRelation` between two `Traversal`s
enum class SizeRelation {
  Same,
  Larger,
  Smaller,
  DontCare
};

/// `Score` is used to represent the score obtained comparing two `Traversal`s.
/// It embeds the criteria we define in order to select the `BestTraversal` that
/// we want to use to rewrite the pointer access.
struct Score {
  bool Valid;
  long StartDistance;
  SizeRelation SizeRelation;
  uint64_t TypeDistance;
  long CommonStrides;
  long Depth;

  static Score invalid();

  std::strong_ordering operator<=>(const Score &Other);
};

Score Score::invalid() {
  return Score{ .Valid = false,
                .StartDistance = 0,
                .SizeRelation = SizeRelation::DontCare,
                .TypeDistance = 0,
                .CommonStrides = 0,
                .Depth = 0 };
}

/// We redefine the spaceship operator in order to define the ordering criteria
/// for comparing `Score`s, which drives the selection of the `BestTraversal`
std::strong_ordering Score::operator<=>(const Score &Other) {

  // An `Invalid` field must be considered `greater` than a `Valid` one
  if (not Valid and Other.Valid) {
    return std::strong_ordering::greater;
  }
  if (Valid and not Other.Valid) {
    return std::strong_ordering::less;
  }
  if (not Valid and not Other.Valid) {
    return std::strong_ordering::equal;
  }

  // When both `Score`s are valid, we move on to comparing:
  // 1) `StartDistance`
  auto Cmp = StartDistance <=> Other.StartDistance;
  if (Cmp != std::strong_ordering::equal) {
    return Cmp;
  }

  // 2) `SizeRelation`
  Cmp = SizeRelation <=> Other.SizeRelation;
  if (Cmp != std::strong_ordering::equal) {
    return Cmp;
  }

  // 3) `TypeDistance`
  Cmp = TypeDistance <=> Other.TypeDistance;
  if (Cmp != std::strong_ordering::equal) {
    return Cmp;
  }

  // 4) `CommonStrides`
  Cmp = Other.CommonStrides <=> CommonStrides;
  if (Cmp != std::strong_ordering::equal) {
    return Cmp;
  }

  // 5) `Depth`
  return Depth <=> Other.Depth;
}

/// The `score` function is used in order to obtain a _similarity_ `Score`
/// between the `Explicit` and `Ideal` `Traversal`s. We want to select the
/// `Traversal` with the minimal score as the one that will constitute the
/// pointer access rewrite
static Score score(const Traversal &Explicit, const Traversal &Ideal) {
  long StartDistance = Explicit.begin() - Ideal.begin();
  long EndDistance = Explicit.end() - Ideal.end();

  long CommonStrides = commonPrefixStrides(Explicit.TraversedArrays,
                                           Ideal.TraversedArrays);
  uint64_t TypeDistValue = typeDistance(Explicit.TargetType, Ideal.TargetType);

  if (StartDistance < 0) {

    // Explicit comes first - invalid
    return Score::invalid();
  } else if (StartDistance == 0) {

    // They start at same point
    if (EndDistance == 0) {

      // We have a perfect match, in this situation we will rely on the other
      // criteria to elect the `BestTraversal`
      return Score{ .Valid = true,
                    .StartDistance = 0,
                    .SizeRelation = SizeRelation::Same,
                    .TypeDistance = TypeDistValue,
                    .CommonStrides = CommonStrides,
                    .Depth = Ideal.depth() };
    } else if (EndDistance < 0) {

      // Explicit ends before Ideal
      return Score{ .Valid = true,
                    .StartDistance = 0,
                    .SizeRelation = SizeRelation::Larger,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Ideal.depth() };
    } else if (EndDistance > 0) {

      // Explicit ends after Ideal
      return Score{ .Valid = true,
                    .StartDistance = 0,
                    .SizeRelation = SizeRelation::Smaller,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Ideal.depth() };
    }
  } else if (StartDistance > 0) {

    // Ideal comes first (StartDistance > 0)
    if (EndDistance <= 0) {

      // Explicit ends before or at Ideal
      return Score{ .Valid = true,
                    .StartDistance = StartDistance,
                    .SizeRelation = SizeRelation::DontCare,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Ideal.depth() };
    } else {

      // Explicit ends after Ideal - partial overlap, invalid
      return Score::invalid();
    }
  }

  // We do not expect that we can reach this point, all the previous case should
  // cover all the possibilities
  revng_abort();
}

// =============================================================================
// `TypeTraversalAnalyzer` class definition
// =============================================================================

/// `TypeTraversalAnalyzer` is used as an oracle to compute and retrieve
/// `Traversal`s and `ArrayPath`s in a lazy manner
class TypeTraversalAnalyzer {
private:
  /// Reference to the cache containing the pre-computed `Traversal`s and
  /// `ArrayPath`s. This passed in the constructor, as we want to cache the
  /// information across different runs
  TraversalInfoMap &Data;

public:
  TypeTraversalAnalyzer(TraversalInfoMap &Data) : Data(Data) {}

public:
  /// Retrieve the precomputed `Traversal`s for `BaseType` (or compute them
  /// on-the-fly`)
  const std::vector<Traversal> &getTraversals(mlir::Type BaseType);

  /// Retrieve the precomputed `ArrayPath`s for `BaseType` (or compute them
  /// on-the-fly`)
  const std::vector<ArrayPath> &getArrayPaths(mlir::Type BaseType);

  /// Retrieve only the slice of `Traversal`s, starting from the `BaseType`,
  /// that are useful for the comparison with the current access described by
  /// `Arithmetic`.
  /// There are two _modes of operation_:
  /// 1) When `SmartLookup` is off, we simply retrieve all the `Traversal`s
  ///    relative to `BaseType`. With this mode of operation, the additional
  ///    parameters are actually useless.
  //// 2) When `SmartLookup` is on, we employ some smarties in order to reduce
  ///     the search space for `Traversal`s that we retrieve.
  //      TODO: this mode of operation is not implemented ATM.
  std::pair<std::vector<Traversal>::const_iterator,
            std::vector<Traversal>::const_iterator>
  getTraversalRange(mlir::Type BaseType,
                    const PointerArithmetic &Arithmetic,
                    const mlir::Type &PointeeType,
                    bool SmartLookup);

private:
  /// Entry point for traversing the `BaseType`, and producing the corresponding
  /// `Traversal`s and `ArrayPaths` (takes care of ordering them)
  llvm::DenseMap<mlir::Type, TraversalInfo>::iterator
  traverse(mlir::Type BaseType);

  /// Underlying `impl` method for performing the recursive step of the traverse
  /// of a `BaseType`. Uses `RecursiveCoroutine` for stack safety.
  RecursiveCoroutine<void>
  traverseImpl(mlir::Type Type,
               std::vector<Traversal> &Traversals,
               std::vector<ArrayPath> &ArrayPaths,
               int64_t CurrentOffset = 0,
               const std::vector<uint64_t> &FieldPath = {},
               const ArrayPath &CurrentArrayPath = {});
};

const std::vector<Traversal> &
TypeTraversalAnalyzer::getTraversals(mlir::Type BaseType) {
  auto It = Data.find(BaseType);
  if (It == Data.end()) {
    It = traverse(BaseType);
  }

  return It->second.Traversals;
}

const std::vector<ArrayPath> &
TypeTraversalAnalyzer::getArrayPaths(mlir::Type BaseType) {
  auto It = Data.find(BaseType);
  if (It == Data.end()) {
    It = traverse(BaseType);
  }

  return It->second.ArrayPaths;
}

std::pair<std::vector<Traversal>::const_iterator,
          std::vector<Traversal>::const_iterator>
TypeTraversalAnalyzer::getTraversalRange(mlir::Type BaseType,
                                         const PointerArithmetic &Arithmetic,
                                         const mlir::Type &PointeeType,
                                         bool SmartLookup) {

  // TODO: for the time being, we do not implement the smart lookup logic, and
  //       therefore we assert that this does not happen until we have added the
  //       implementation
  if (not SmartLookup) {
    const std::vector<Traversal> &Traversals = getTraversals(BaseType);
    return { Traversals.begin(), Traversals.end() };
  }

  revng_abort("Fast lookup not implemented");
}

llvm::DenseMap<mlir::Type, TraversalInfo>::iterator
TypeTraversalAnalyzer::traverse(mlir::Type BaseType) {
  revng_assert(Data.count(BaseType) == 0);

  auto [It, Inserted] = Data.insert({ BaseType, TraversalInfo() });
  auto &[Traversals, ArrayPaths] = It->second;

  // Add the empty `ArrayPath` representing the case where no `array` is
  // traversed. This ensures that `toExplicitArrayAccesses` can produce
  // explicit `Arithmetic`s even when no array traversal is involved.
  ArrayPaths.push_back(ArrayPath());

  // Recursively traverse the `BaseType` to populate `Traversal`s and
  // `ArrayPath`s
  rc_eval(traverseImpl(BaseType, Traversals, ArrayPaths));

  // Sort traversals by `StartOffset`, then by `Size` of the `TargetType`
  std::sort(Traversals.begin(),
            Traversals.end(),
            [](const Traversal &A, const Traversal &B) {
              if (A.StartOffset != B.StartOffset) {
                return A.StartOffset < B.StartOffset;
              } else {
                return getTypeSize(A.TargetType) < getTypeSize(B.TargetType);
              }
            });

  // Sort `ArrayPath`s by `Stride`, larger first
  for (auto &Path : ArrayPaths) {
    std::sort(Path.begin(),
              Path.end(),
              [](const NestedArrayShape &A, const NestedArrayShape &B) {
                return A.Stride > B.Stride;
              });
  }

  return It;
}

RecursiveCoroutine<void>
TypeTraversalAnalyzer::traverseImpl(mlir::Type Type,
                                    std::vector<Traversal> &Traversals,
                                    std::vector<ArrayPath> &ArrayPaths,
                                    int64_t CurrentOffset,
                                    const std::vector<uint64_t> &FieldPath,
                                    const ArrayPath &CurrentArrayPath) {

  // We should never reach a type with zero size - if we do, it means there is
  // something severely wrong in the types we're working with
  revng_assert(getTypeSize(Type) > 0);

  // Helper to add a `Traversal` landing on the current type at the current
  // position in the traversal
  auto AddTraversal = [&](mlir::Type TargetType) {
    Traversal T;
    T.TargetType = TargetType;
    T.StartOffset = CurrentOffset;
    T.LeftoverOffset = 0;
    T.TraversedFields = FieldPath;
    T.TraversedArrays = arrayPathToSortedVector(CurrentArrayPath);
    Traversals.push_back(T);
  };

  if (auto PrimitiveType = Type.dyn_cast<clift::PrimitiveType>()) {
    // `PrimitiveType` is a leaf node in our traversal
    AddTraversal(PrimitiveType);
    rc_return;
  }

  // `PointerType` is a leaf node in our traversal: we do not traverse
  // through pointers, but we still want to produce a `Traversal` that
  // lands on a field whose type is a pointer
  if (auto Pointer = Type.dyn_cast<clift::PointerType>()) {
    AddTraversal(Pointer);
    rc_return;
  }

  // Traverse each `typedef`
  if (auto Typedef = Type.dyn_cast<clift::TypedefType>()) {
    AddTraversal(Typedef);
    clift::ValueType UnderlyingType = Typedef.getUnderlyingType();
    rc_recur traverseImpl(UnderlyingType.cast<mlir::Type>(),
                          Traversals,
                          ArrayPaths,
                          CurrentOffset,
                          FieldPath,
                          CurrentArrayPath);
    rc_return;
  }

  // Traverse the `array`
  if (auto ArrayType = Type.dyn_cast<clift::ArrayType>()) {
    AddTraversal(ArrayType);
    clift::ValueType ElementType = ArrayType.getElementType();
    uint64_t NumElements = ArrayType.getElementsCount();
    uint64_t ElementSize = ElementType.getByteSize();

    // Add this array to the current array path
    NestedArrayShape ArrayInfo;
    ArrayInfo.OffsetFromParentArrayElement = 0;
    ArrayInfo.Stride = ElementSize;
    ArrayInfo.NumElements = NumElements;

    ArrayPath NewArrayPath = CurrentArrayPath;
    if (!NewArrayPath.empty()) {

      // Adjust `OffsetFromParentArray` for nested arrays
      ArrayInfo
        .OffsetFromParentArrayElement = CurrentOffset
                                        - (NewArrayPath.back()
                                             .OffsetFromParentArrayElement);
    } else {
      ArrayInfo.OffsetFromParentArrayElement = CurrentOffset;
    }
    NewArrayPath.push_back(ArrayInfo);

    // Record this array path
    ArrayPaths.push_back(NewArrayPath);

    // Traverse into the first element of the array
    rc_recur traverseImpl(ElementType.cast<mlir::Type>(),
                          Traversals,
                          ArrayPaths,
                          CurrentOffset,
                          FieldPath,
                          NewArrayPath);
    rc_return;
  }

  // Traverse `struct` or `union` (both implement `ClassType`).
  // For `union`s, `Field.getOffset()` always returns 0 by verification.
  if (auto ClassType = mlir::dyn_cast<clift::ClassType>(Type)) {
    AddTraversal(ClassType);
    llvm::ArrayRef<clift::FieldAttr> Fields = ClassType.getFields();
    for (size_t I = 0; I < Fields.size(); ++I) {
      clift::FieldAttr Field = Fields[I];
      clift::ValueType FieldType = Field.getType();
      int64_t FieldOffset = CurrentOffset + Field.getOffset();

      std::vector<uint64_t> NewFieldPath = FieldPath;
      NewFieldPath.push_back(static_cast<uint64_t>(I));

      rc_recur traverseImpl(FieldType.cast<mlir::Type>(),
                            Traversals,
                            ArrayPaths,
                            FieldOffset,
                            NewFieldPath,
                            CurrentArrayPath);
    }
    rc_return;
  }

  // Traverse the `enum`
  if (auto EnumType = Type.dyn_cast<clift::EnumType>()) {

    // We traverse the underlying `EnumType`
    clift::ValueType UnderlyingType = EnumType.getUnderlyingType();

    // Add traversal for the `enum` itself
    AddTraversal(EnumType);

    // Also traverse into the underlying type inside the `enum
    rc_recur traverseImpl(UnderlyingType.cast<mlir::Type>(),
                          Traversals,
                          ArrayPaths,
                          CurrentOffset,
                          FieldPath,
                          CurrentArrayPath);
    rc_return;
  }
}

// =============================================================================
// `BestTraversalChooser` class definition
// =============================================================================

/// `BestTraversalChooser` is used as a compute class for the `BestTraversal`
class BestTraversalChooser {
private:
  /// The `TypeTraversalAnalyzer` is our `Traversal` and `ArrayPath` oracle
  TypeTraversalAnalyzer TraversalAnalyzer;

public:
  /// We need an explicit constructor in order to propagate the
  /// `TraversalInfoMap` which is used as a global cache for storing
  /// `Traversal`s and `ArrayPath`s
  BestTraversalChooser(TraversalInfoMap &Data) : TraversalAnalyzer(Data) {}

public:
  /// Public entry point for computing the `BestTraversal` for the
  /// `PointerToReplace` and the pre-computed `Arithmetic`
  std::optional<Traversal>
  computeBestTraversal(ExpressionOpInterface PointerToReplace,
                       const PointerArithmetic &Arithmetic);

private:
  /// Obtain the explicit rewrite of the constant folded portion of
  /// `Arithmetic`, following an array traversal described by `ArrayPath`, so
  /// that it is evident in the `LinearCombination` component of `Arithmetic`
  std::optional<PointerArithmetic>
  getExplicitArithmetic(const PointerArithmetic &Arithmetic,
                        const ArrayPath &ArrayPath);

  /// Obtain all the explicit rewritings of the input `Arithmetic` following all
  /// the `ArrayPath`s for the `BaseType`
  std::vector<PointerArithmetic>
  toExplicitArrayAccesses(const PointerArithmetic &Arithmetic);

  /// Helper which trivially spill a `PointerArithmetic` into a `Traversal`
  Traversal toTraversal(const PointerArithmetic &PA,
                        const mlir::Type &PointeeType,
                        const Traversal &Ideal);

  /// Obtain the best `Traversal`
  std::optional<Traversal>
  getBestTraversal(mlir::Type BaseType,
                   mlir::Type PointeeType,
                   const std::vector<PointerArithmetic> &ExplicitArithmetics);
};

std::optional<Traversal>
BestTraversalChooser::computeBestTraversal(ExpressionOpInterface
                                             PointerToReplace,
                                           const PointerArithmetic
                                             &Arithmetic) {
  // We only perform the substitution for `PointerType`
  auto PointerToReplaceType = PointerToReplace->getResult(0).getType();
  if (not isPointerType(PointerToReplaceType)) {
    return std::nullopt;
  }

  // Expand to explicit array accesses the input `PointerArithmetic`, so that
  // the constant folded component performed by the compiler is evident in the
  // `LinearCombination` portion of `Arithmetic`
  std::vector<PointerArithmetic>
    ExplicitArithmetics = toExplicitArrayAccesses(Arithmetic);

  mlir::Type PointeeType = PointerToReplaceType.cast<PointerType>()
                             .getPointeeType();
  auto BasePtrType = getPointerType(Arithmetic.BasePointer.getType());
  revng_assert(BasePtrType);
  auto BaseType = BasePtrType.getPointeeType();

  // Obtain the `BestTraversal` for connecting `BaseType` to `PointeeType`,
  // following one of the possible `ExplicitArithmetic`s
  auto BestTraversal = getBestTraversal(BaseType,
                                        PointeeType,
                                        ExplicitArithmetics);

  // TODO: evaluate the early stop criterion below:
  // In case we have a array, every time we manage a pointer to the array, we
  // would a `PointerArithmetic` with a zero `BaseOffset` and no
  // `LinearCombination`, and a `BestTraversal` composed by a single
  // `TraversedArray`, which points to the trivial first element of the `array`.
  // We do not want to perform the rewrite in this case.
  if (Arithmetic.Offset.BaseOffset == 0
      and Arithmetic.Offset.LinearCombination.empty()) {
    if (BestTraversal->TraversedArrays.size() == 1
        and BestTraversal->TraversedFields.size() == 0) {
      return std::nullopt;
    }
  }

  // In case we end up with a `BestTraversal` which does not actually traverse
  // any `struct` field or `array` element, we avoid the rewriting altogether,
  // and we leave the explicit pointer arithmetic access in `clift`
  if (BestTraversal->isShallow()) {
    return std::nullopt;
  }

  return BestTraversal;
}

// Turn the input `Arithmetic` into another `PointerArithmetic` , following the
// array traversal dictaded by the `ArrayPath` `AP`. On success, the output
// `PointerArithmetic` has a `StartOffset` that is lower than or equal than the
// input one, and all the array traversals of `AP` have an equivalent
// `StridedTerm` in the `LinearCombination` of `OffsetExpression` of the
// `Result`.
// For example this can turn P + 12 (with no `LinearCombination`) into
// P + 8 * 1 + 4 (with a single `StridedTerm`, with fixed `Index`) if `AP` is
// e.g. `{.OffsetFromParentArrayElement = 0, .EndOffset = 48, .Stride = 8}`)
std::optional<PointerArithmetic>
BestTraversalChooser::getExplicitArithmetic(const PointerArithmetic &Arithmetic,
                                            const ArrayPath &AP) {

  // Recover the `PointerBitSize` from the computed `PointerArithmetic`, so we
  // have centralized place for computing it
  unsigned PointerBitSize = Arithmetic.PointerBitSize;

  PointerArithmetic Result(PointerBitSize);
  Result.BasePointer = Arithmetic.BasePointer;

  // We do not modify the input `Arithmetic`, but we work on a local copy
  PointerArithmetic WorkingArithmetic = Arithmetic;

  for (const NestedArrayShape &NAI : AP) {
    const auto &[OffsetFromParentArrayElement, NumElements, Stride] = NAI;

    // Consume the offset from the parent array element
    Result.Offset.BaseOffset += OffsetFromParentArrayElement;

    revng_assert(WorkingArithmetic.Offset.BaseOffset
                   .uge(OffsetFromParentArrayElement));
    llvm::APInt OffsetInsideArray = WorkingArithmetic.Offset.BaseOffset
                                    - OffsetFromParentArrayElement;
    WorkingArithmetic.Offset.BaseOffset = OffsetInsideArray;

    // If, after adjusting `StartOffset`, the `StartOffset` of `Arithmetic` is
    // still larger than the `Stride` coming from `NAI`, we have to take that
    // into account and add to the `Result` a constant `StridedTerm`
    auto &LC = Result.Offset.LinearCombination;

    // `Stride`s must be in non-ascending order (equal strides are allowed for
    // nested arrays with the same element size, e.g., int array[1][1])
    revng_assert(LC.empty() or LC.back().Stride.uge(Stride));

    llvm::APInt IndexConstantComponent = llvm::APInt(PointerBitSize, 0);
    if (WorkingArithmetic.Offset.BaseOffset.uge(Stride)) {
      IndexConstantComponent = WorkingArithmetic.Offset.BaseOffset.udiv(Stride);
      revng_assert(IndexConstantComponent.ult(NumElements));
      WorkingArithmetic.Offset.BaseOffset = WorkingArithmetic.Offset.BaseOffset
                                              .urem(Stride);
    }

    mlir::Value IndexVariableComponent = {};

    // If the `PointerArithmetic` is doing a variable-index array traversal with
    // a stride that differs from NAI, then we have to bail out. Either a
    // subsequent `ArrayPath` will hit the sweet spot, or none will, but that's
    // not something we have to handle here.
    if (not WorkingArithmetic.Offset.LinearCombination.empty()) {
      if (WorkingArithmetic.Offset.LinearCombination.front()
            .Stride.ugt(Stride)) {
        return std::nullopt;
      }
      if (Stride == WorkingArithmetic.Offset.LinearCombination.front().Stride) {
        auto &FrontTerm = WorkingArithmetic.Offset.LinearCombination.front();
        IndexVariableComponent = FrontTerm.Idx.Variable;

        // If the index also has a constant component, sum it into the
        // `IndexConstantComponent` we are building
        if (FrontTerm.Idx.Constant.getBoolValue()) {
          IndexConstantComponent += FrontTerm.Idx.Constant;
        }

        WorkingArithmetic.Offset.LinearCombination
          .erase(WorkingArithmetic.Offset.LinearCombination.begin());
      }
    }

    // We add a new term to the constructed `LinearCombination`, using the
    // `Index` components identified
    LC.push_back(PointerArithmetic::StridedTerm(llvm::APInt(PointerBitSize,
                                                            Stride),
                                                { IndexVariableComponent,
                                                  IndexConstantComponent }));
  }

  // If we were not able to consume all the `LinerCombination`s of the input
  // `Arithmetic`, we bail out
  if (not WorkingArithmetic.Offset.LinearCombination.empty()) {
    return std::nullopt;
  }

  // If we still have some non-consumed portion of the input `BaseOffset`, we
  // propagate it in the `Result`
  if (WorkingArithmetic.Offset.BaseOffset.getBoolValue()) {
    Result.Offset.BaseOffset += WorkingArithmetic.Offset.BaseOffset;
  }

  return Result;
}

std::vector<PointerArithmetic>
BestTraversalChooser::toExplicitArrayAccesses(const PointerArithmetic
                                                &Arithmetic) {
  std::vector<PointerArithmetic> Result;

  auto BasePtrType = getPointerType(Arithmetic.BasePointer.getType());
  revng_assert(BasePtrType);
  auto BaseType = BasePtrType.getPointeeType();

  // We retrieve all the `ArrayPath`s that we can build from `BaseType`
  const std::vector<ArrayPath> &ArrayPaths = TraversalAnalyzer
                                               .getArrayPaths(BaseType);

  // We now filter the `ArrayPath`s by taking into consideration only those that
  // are compatible with the `BaseOffset` access present in the
  // `PointerArithmetic` that we are considering
  auto CompatibleArrayPaths = findCompatibleArrayPaths(ArrayPaths,
                                                       Arithmetic.Offset
                                                         .BaseOffset);

  for (const ArrayPath *TheArrayPath : CompatibleArrayPaths) {

    // Try and turn `Arithmetic` into a form where all array indexes, even the
    // constant ones, are explicit. In case of success, we enqueue the
    // `Explicit` in the final `Result`s
    std::optional<PointerArithmetic>
      Explicit = getExplicitArithmetic(Arithmetic, *TheArrayPath);
    if (Explicit) {
      Result.push_back(std::move(*Explicit));
    }
  }

  return Result;
}

Traversal BestTraversalChooser::toTraversal(const PointerArithmetic &PA,
                                            const mlir::Type &PointeeType,
                                            const Traversal &Ideal) {

  // We want to turn an explicit `PointerArithmetic` `PA` in a `Traversal`,
  // assuming that it does the traversal described in `Ideal`
  Traversal Result = Ideal;

  // Because `PA` is explicit (i.e. all array traversals at fixed index have
  // been expanded in the `LinearCombination`), the `Result` `Traversal` will
  // always be the same, except that we have to adjust the leftover offset
  Result.LeftoverOffset = PA.Offset.BaseOffset.getZExtValue()
                          - Ideal.StartOffset;

  // Fix the `TargetType` to the actual type that is required by the traversal
  // on `clift` IR
  Result.TargetType = PointeeType;

  return Result;
}

// To find the `BestTraversal`, we have to compare all the valid `Traversal`s
// from `BaseType` with all the ones that we can build from the
// `ExplicitArithmetic`s we get from `clift`.
std::optional<Traversal>
BestTraversalChooser::getBestTraversal(mlir::Type BaseType,
                                       mlir::Type PointeeType,
                                       const std::vector<PointerArithmetic>
                                         &ExplicitArithmetics) {

  std::optional<Traversal> BestTraversal = std::nullopt;
  Score BestScore = Score::invalid();

  // The `Traversal`s are lazily computed upon first inspection of a `BaseType`
  const std::vector<Traversal> &Traversals = TraversalAnalyzer
                                               .getTraversals(BaseType);

  for (const PointerArithmetic &Explicit : ExplicitArithmetics) {

    // Get the range of `Traversal`s to compare from the `TraversalAnalyzer`.
    // There are two modes of operation for this: with `SmartLookup`, or
    // without.
    // ATM only `SmartLookup` is not implemented. Once it is however,
    // in the tests we want to double check that the results obtained are the
    // SAME both if `SmartLookup` enabled and disabled.
    auto [Begin, End] = TraversalAnalyzer.getTraversalRange(BaseType,
                                                            Explicit,
                                                            PointeeType,
                                                            false);
    for (auto It = Begin; It != End; ++It) {
      const Traversal &Ideal = *It;

      // Convert each `ExplicitArithemtic` into a `Traversal`, so we can compare
      // it with `Ideal`. `ExplicitTraversal` is the `Traversal` that we
      // would obtain traversing the `BaseType` with `Explicit` if we did
      // traverse it as the `Ideal` suggests. Basically what can be
      // different is just the `LeftOverOffset`.
      Traversal ExplicitTraversal = toTraversal(Explicit, PointeeType, Ideal);

      Score CurrentScore = score(ExplicitTraversal, Ideal);

      if (!CurrentScore.Valid)
        continue;

      // We select the `Score` which best suits the criteria defining in the
      // _scoring_ mechanism
      if (CurrentScore < BestScore) {
        BestScore = CurrentScore;
        BestTraversal = ExplicitTraversal;
      }
    }
  }

  // We serialize on the `Log` the selected `BestTraversal`
  if (Log.isEnabled() and BestTraversal) {
    Log << "Elected  BestTraversal:\n";
    BestTraversal->dump();
  }

  // If no `Traversal` was valid, we'll return a `nullopt` here, meaning that we
  // will not replace the `PointerToReplace` with a field access. This basically
  // means that all the possible `Traversal`s that the clift expression could
  // represent are so ugly that we bail out.
  return BestTraversal;
}

} // namespace

std::optional<Traversal>
computeBestTraversal(ExpressionOpInterface PointerToReplace,
                     const PointerArithmetic &Arithmetic,
                     TraversalInfoMap &Data) {
  auto BestTraversalC = BestTraversalChooser(Data);
  return BestTraversalC.computeBestTraversal(PointerToReplace, Arithmetic);
}
