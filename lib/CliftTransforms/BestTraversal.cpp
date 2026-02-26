//
// This file is distributed under the MIT License. See LICENSE.md for details.
//
#include <compare>
#include <cstdint>
#include <memory>
#include <optional>

#include "llvm/ADT/STLExtras.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"

#include "revng/Clift/CliftEnums.h"
#include "revng/CliftTransforms/BestTraversal.h"
#include "revng/CliftTransforms/EmitFieldAccesses.h"
#include "revng/CliftTransforms/Passes.h"
#include "revng/CliftTransforms/PointerArithmetic.h"
#include "revng/Support/Assert.h"
#include "revng/Support/CTarget.h"

namespace clift = mlir::clift;
using namespace clift;

static Logger Log("best-traversal");

namespace {

// =============================================================================
// Static helper functions
// =============================================================================

/// Helper function used to retrieve the byte size of any `mlir::Type`
static uint64_t getTypeSize(mlir::Type Type) {
  if (auto PrimitiveType = Type.dyn_cast<clift::PrimitiveType>()) {
    return PrimitiveType.getByteSize();
  }

  if (auto PointerType = Type.dyn_cast<clift::PointerType>()) {
    return PointerType.getByteSize();
  }

  if (auto ArrayType = Type.dyn_cast<clift::ArrayType>()) {
    return ArrayType.getByteSize();
  }

  if (auto StructType = Type.dyn_cast<clift::StructType>()) {
    return StructType.getSize();
  }

  if (auto UnionType = Type.dyn_cast<clift::UnionType>()) {
    return UnionType.getSize();
  }

  if (auto EnumType = Type.dyn_cast<clift::EnumType>()) {
    return EnumType.getByteSize();
  }

  if (auto TypedefType = Type.dyn_cast<clift::TypedefType>()) {
    return TypedefType.getByteSize();
  }

  // Abort if we encounter an unexpected type here
  revng_abort();
}

/// Helper function which converts a generic `ArrayPath` to a compatible form
/// used to store the `array` traversal into the `Traversal` class. The
/// re-ordering in descending `Stride` order is provided by the comparison
/// operator of `ArrayShape`
static std::set<ArrayShape> arrayPathToSet(const ArrayPath &Path) {
  std::set<ArrayShape> Result;
  for (const NestedArrayShape &Nested : Path) {
    ArrayShape Shape;
    Shape.NumElements = Nested.NumElements;
    Shape.Stride = Nested.Stride;
    Result.insert(Shape);
  }
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
static std::vector<const ArrayPath *>
findCompatibleArrayPaths(const std::vector<ArrayPath> &AllArrayPaths,
                         const llvm::APInt &BaseOffset) {
  std::vector<const ArrayPath *> CompatibleArrays;
  for (const ArrayPath &Path : AllArrayPaths) {
    if (isCompatible(Path, BaseOffset))
      CompatibleArrays.push_back(&Path);
  }
  return CompatibleArrays;
}

/// Helper function which counts the number of common `Stride`s
static int64_t commonPrefixStrides(const std::set<uint64_t> &LHS,
                                   const std::set<uint64_t> &RHS) {
  int64_t Count = 0;
  auto LIt = LHS.begin();
  auto RIt = RHS.begin();

  // We iterate in parallel on both the LHS and RHS and count the `Strides`
  // which match in size between both of them. This can be done since the
  // `Stride`s are in descending order.
  while (LIt != LHS.end() && RIt != RHS.end()) {
    if (*LIt == *RIt) {
      ++Count;
      ++LIt;
      ++RIt;
    } else if (*LIt > *RIt) {
      ++LIt;
    } else {
      ++RIt;
    }
  }

  return Count;
}

} // namespace

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

bool ArrayShape::operator==(const ArrayShape &Other) const {
  return Stride == Other.Stride && NumElements == Other.NumElements;
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

std::set<uint64_t> Traversal::getStrides() const {
  std::set<uint64_t> Strides;
  for (const auto &Shape : TraversedArrays) {
    Strides.insert(Shape.Stride);
  }
  return Strides;
}

bool Traversal::empty() const {
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
/// To compute the distance, we traverse this lattice from LHS to RHS.
/// Whenever we have to walk upwards, we weight each step upward 1.
class TypeDistanceLatticeCompute {

  // Define lattice node types for classification
  enum class LatticeNode {
    SpecificEnum,
    Unsigned,
    Signed,
    Float,
    SpecificPointer,
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
      return LatticeNode::SpecificEnum;
    }

    if (T.isa<PointerType>()) {
      return LatticeNode::SpecificPointer;
    }

    // Shouldn't reach here given earlier checks
    revng_abort("We cannot identify suitable `LatticeNode` for `Type` `T`");
  };

  // Helper function to get the distance to a common ancestor
  long getDistanceToNode(LatticeNode From, LatticeNode To) {
    auto Ancestors = getAncestors(From);

    // We walk up the list of ancenstors counting the steps
    for (auto [I, Ancestor] : llvm::enumerate(Ancestors)) {
      if (Ancestor == To)
        return I;
    }

    // In case we found no path from `From` to `To` we return a placeholder
    // value
    return std::numeric_limits<long>::max();
  }

  // Helper method which returns the ordered list of `Ancestor`s of a
  // `LatticeNode`
  std::vector<LatticeNode> getAncestors(LatticeNode N) {
    using LN = LatticeNode;
    switch (N) {
    case LN::SpecificEnum:
      return { LN::SpecificEnum,
               LN::Unsigned,
               LN::Number,
               LN::PointerOrNumber,
               LN::Generic };
    case LN::Unsigned:
      return { LN::Unsigned, LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::Signed:
      return { LN::Signed, LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::Number:
      return { LN::Number, LN::PointerOrNumber, LN::Generic };
    case LN::SpecificPointer:
      return { LN::SpecificPointer, LN::PointerOrNumber, LN::Generic };
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

    // At this point, `A == B` can only be only in case we have `SpecificEnum`
    // or `SpecificPointer` (because they are two distinct type of the same
    // family). Identical primitive type are caught by the `LHS == RHS` early
    // exit check in `typeDistance`.
    if (A == B) {
      revng_assert(A == LatticeNode::SpecificEnum
                   or A == LatticeNode::SpecificPointer);
    }

    // For each node, its ordered ancestor chain from self to `Generic`
    // (inclusive). SpecificEnum/SpecificPointer represent *families* of
    // distinct types, so when A == B for these, the LCA is their parent
    // (handled via SameFamily). The
    auto AncestorsA = getAncestors(A);
    auto AncestorsB = getAncestors(B);
    std::set<LatticeNode> SetB(AncestorsB.begin(), AncestorsB.end());

    // When A == B, it can only be `SpecificEnum` or `SpecificPointer`.
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
  long getTypeDistance(mlir::Type LHS, mlir::Type RHS) {
    // Classify both types
    LatticeNode LHSNode = classifyType(LHS);
    LatticeNode RHSNode = classifyType(RHS);

    // Find their least common ancestor (LCA)
    LatticeNode LCA = findLCA(LHSNode, RHSNode);

    // Distance is defined as the number of upward steps from LHS to LCA
    long Distance = getDistanceToNode(LHSNode, LCA);

    return Distance;
  }
};

/// The `typeDistance` function is a helper function which computes the defined
/// `TypeDistance`, according to the following criteria:
/// If the sizes of the input types differ, this distance is just "infinity". If
/// the inputs are not scalar, this distance is also "infinity". If they're both
/// scalars we should use the lattice approach, based on the primitives but
/// extended with enums and pointers. Typdefs are ignored. In such case, we
/// employ the `TypeDistanceLatticeCompute` helper class to perform the
/// computation.
static long typeDistance(mlir::Type LHS, mlir::Type RHS) {

  // First, unwrap any typedefs as they should be traversed in order to reach
  // the underlying type
  while (auto TypedefLHS = LHS.dyn_cast<TypedefType>()) {
    LHS = TypedefLHS.getUnderlyingType().cast<mlir::Type>();
  }
  while (auto TypedefRHS = RHS.dyn_cast<TypedefType>()) {
    RHS = TypedefRHS.getUnderlyingType().cast<mlir::Type>();
  }

  // If sizes differ, the `TypeDistance` is infinity
  if (getTypeSize(LHS) != getTypeSize(RHS)) {
    return std::numeric_limits<long>::max();
  }

  // Check if both are _scalars_, as defined on the lattice (`primitive`, `enum`
  // or `pointer`)
  bool LHSIsScalar = LHS.isa<PrimitiveType>() || LHS.isa<EnumType>()
                     || LHS.isa<PointerType>();
  bool RHSIsScalar = RHS.isa<PrimitiveType>() || RHS.isa<EnumType>()
                     || RHS.isa<PointerType>();

  // If only one is _scalar_, the distance is defined as infinity
  if (!LHSIsScalar || !RHSIsScalar) {
    return std::numeric_limits<long>::max();
  }

  // If they're exactly the same type, `TypeDistance` is 0
  if (LHS == RHS) {
    return 0;
  }

  // In all the other cases, we compute the `TypeDistance` using an ad-hoc
  // lattice
  TypeDistanceLatticeCompute TDC;
  return TDC.getTypeDistance(LHS, RHS);
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
  long TypeDistance;
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

/// We redefine the spaceship operator in order to
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
/// between the `Explicit` and `Candidate` `Traversal`s. We want to select the
/// `Traversal` with the minimal score as the one that will constitute the
/// pointer access rewrite
static Score score(const Traversal &Explicit, const Traversal &Candidate) {
  long StartDistance = Explicit.begin() - Candidate.begin();
  long EndDistance = Explicit.end() - Candidate.end();

  auto ExplicitStrides = Explicit.getStrides();
  auto CandidateStrides = Candidate.getStrides();
  long CommonStrides = commonPrefixStrides(ExplicitStrides, CandidateStrides);
  long TypeDistValue = typeDistance(Explicit.TargetType, Candidate.TargetType);

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
                    .Depth = Candidate.depth() };
    } else if (EndDistance < 0) {

      // Explicit ends before Candidate
      return Score{ .Valid = true,
                    .StartDistance = 0,
                    .SizeRelation = SizeRelation::Larger,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Candidate.depth() };
    } else if (EndDistance > 0) {

      // Explicit ends after Candidate
      return Score{ .Valid = true,
                    .StartDistance = 0,
                    .SizeRelation = SizeRelation::Smaller,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Candidate.depth() };
    }
  } else if (StartDistance > 0) {

    // Candidate comes first (StartDistance > 0)
    if (EndDistance <= 0) {

      // Explicit ends before or at Candidate
      return Score{ .Valid = true,
                    .StartDistance = StartDistance,
                    .SizeRelation = SizeRelation::DontCare,
                    .TypeDistance = 0,
                    .CommonStrides = 0,
                    .Depth = Candidate.depth() };
    } else {

      // Explicit ends after Candidate - partial overlap, invalid
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
  /// of a `BaseType`
  void traverseImpl(mlir::Type Type,
                    std::vector<Traversal> &Traversals,
                    std::vector<ArrayPath> &ArrayPaths,
                    int64_t CurrentOffset = 0,
                    std::vector<uint32_t> FieldPath = {},
                    ArrayPath CurrentArrayPath = {});
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

  revng_assert(not SmartLookup, "Fast lookup not implemented");
  revng_abort("Not reachable path");
}

llvm::DenseMap<mlir::Type, TraversalInfo>::iterator
TypeTraversalAnalyzer::traverse(mlir::Type BaseType) {
  revng_assert(Data.count(BaseType) == 0);

  auto [It, Inserted] = Data.insert({ BaseType, TraversalInfo() });
  auto &[Traversals, ArrayPaths] = It->second;

  // Recursively traverse the `BaseType` to populate `Traversal`s and
  // `ArrayPath`s
  traverseImpl(BaseType, Traversals, ArrayPaths);

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

void TypeTraversalAnalyzer::traverseImpl(mlir::Type Type,
                                         std::vector<Traversal> &Traversals,
                                         std::vector<ArrayPath> &ArrayPaths,
                                         int64_t CurrentOffset,
                                         std::vector<uint32_t> FieldPath,
                                         ArrayPath CurrentArrayPath) {

  if (auto PrimitiveType = Type.dyn_cast<clift::PrimitiveType>()) {

    // `PrimitiveType` is a leaf node in our traversal
    if (PrimitiveType.getByteSize() == 0)
      return;

    Traversal T;
    T.TargetType = PrimitiveType;
    T.StartOffset = CurrentOffset;
    T.LeftoverOffset = 0;
    T.TraversedFields = FieldPath;
    T.TraversedArrays = arrayPathToSet(CurrentArrayPath);
    Traversals.push_back(T);
    return;
  }

  // Traverse the `array`
  if (auto ArrayType = Type.dyn_cast<clift::ArrayType>()) {
    clift::ValueType ElementType = ArrayType.getElementType();
    uint64_t NumElements = ArrayType.getElementsCount();
    uint64_t ElementSize = ElementType.getByteSize();

    if (ElementSize == 0)
      return;

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
    traverseImpl(ElementType.cast<mlir::Type>(),
                 Traversals,
                 ArrayPaths,
                 CurrentOffset,
                 FieldPath,
                 NewArrayPath);
    return;
  }

  if (auto StructType = Type.dyn_cast<clift::StructType>()) {

    // Only traverse if the `struct` is complete (has a definition)
    if (!StructType.isComplete())
      return;

    // Add the `Traversal` for the `struct` itself
    if (StructType.getSize() > 0) {
      Traversal T;
      T.TargetType = StructType;
      T.StartOffset = CurrentOffset;
      T.LeftoverOffset = 0;
      T.TraversedFields = FieldPath;
      T.TraversedArrays = arrayPathToSet(CurrentArrayPath);
      Traversals.push_back(T);
    }

    // Traverse each field
    llvm::ArrayRef<clift::FieldAttr> Fields = StructType.getFields();
    for (size_t I = 0; I < Fields.size(); ++I) {
      clift::FieldAttr Field = Fields[I];
      clift::ValueType FieldType = Field.getType();
      int64_t FieldOffset = CurrentOffset + Field.getOffset();

      std::vector<uint32_t> NewFieldPath = FieldPath;
      NewFieldPath.push_back(static_cast<uint32_t>(I));

      traverseImpl(FieldType.cast<mlir::Type>(),
                   Traversals,
                   ArrayPaths,
                   FieldOffset,
                   NewFieldPath,
                   CurrentArrayPath);
    }
    return;
  }

  if (auto UnionType = Type.dyn_cast<clift::UnionType>()) {

    // Only traverse if the `union` is complete (has definition)
    if (!UnionType.isComplete())
      return;

    // Add `Traversal` for the `union` itself
    if (UnionType.getSize() > 0) {
      Traversal T;
      T.TargetType = UnionType;
      T.StartOffset = CurrentOffset;
      T.LeftoverOffset = 0;
      T.TraversedFields = FieldPath;
      T.TraversedArrays = arrayPathToSet(CurrentArrayPath);
      Traversals.push_back(T);
    }

    // For `union`s, all their fields start at the same `Offset`
    llvm::ArrayRef<clift::FieldAttr> Fields = UnionType.getFields();
    for (size_t I = 0; I < Fields.size(); ++I) {
      clift::FieldAttr Field = Fields[I];
      clift::ValueType FieldType = Field.getType();

      // `union` fields all start at `CurrentOffset`
      int64_t FieldOffset = CurrentOffset;

      std::vector<uint32_t> NewFieldPath = FieldPath;
      NewFieldPath.push_back(static_cast<uint32_t>(I));

      traverseImpl(FieldType.cast<mlir::Type>(),
                   Traversals,
                   ArrayPaths,
                   FieldOffset,
                   NewFieldPath,
                   CurrentArrayPath);
    }
    return;
  }

  if (auto EnumType = Type.dyn_cast<clift::EnumType>()) {

    // We traverse the underlying `EnumType`
    clift::ValueType UnderlyingType = EnumType.getUnderlyingType();

    // Add traversal for the `enum` itself
    if (EnumType.getByteSize() > 0) {
      Traversal T;
      T.TargetType = EnumType;
      T.StartOffset = CurrentOffset;
      T.LeftoverOffset = 0;
      T.TraversedFields = FieldPath;
      T.TraversedArrays = arrayPathToSet(CurrentArrayPath);
      Traversals.push_back(T);
    }

    // Also traverse into the underlying type inside the `enum
    traverseImpl(UnderlyingType.cast<mlir::Type>(),
                 Traversals,
                 ArrayPaths,
                 CurrentOffset,
                 FieldPath,
                 CurrentArrayPath);
    return;
  }
}

// =============================================================================
// `BestTraversalChooser` class definition
// =============================================================================

/// `BestTraversalChooser` is used as a compute class for the `BestTraversal`
class BestTraversalChooser {
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
  /// The `TypeTraversalAnalyzer` is our `Traversal` and `ArrayPath` oracle
  TypeTraversalAnalyzer TraversalAnalyzer;

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
                        const Traversal &Candidate);

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
  if (not PointerToReplaceType.isa<PointerType>()) {
    return std::nullopt;
  }

  // Expand to explicit array accesses the input `PointerArithmetic`, so that
  // the constant folded component performed by the compiler is evident in the
  // `LinearCombination` portion of `Arithmetic`
  std::vector<PointerArithmetic>
    ExplicitArithmetics = toExplicitArrayAccesses(Arithmetic);
  ExplicitArithmetics.push_back(Arithmetic);

  mlir::Type PointeeType = PointerToReplaceType.cast<PointerType>()
                             .getPointeeType();
  auto BasePtrType = Arithmetic.BasePointer.getType().cast<PointerType>();
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
  if (BestTraversal->empty()) {
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
  PointerArithmetic Result = {
    .BasePointer = Arithmetic.BasePointer,
    .Offset = PointerArithmetic::OffsetExpression(),
  };

  // We do not modify the input `Arithmetic`, but we work on a local copy
  PointerArithmetic WorkingArithmetic = Arithmetic;

  for (const NestedArrayShape &NAI : AP) {
    const auto &[OffsetFromParentArrayElement, NumElements, Stride] = NAI;

    // Consume the offset from the parent array element
    Result.Offset.BaseOffset += OffsetFromParentArrayElement;

    revng_assert(llvm::APInt(64, OffsetFromParentArrayElement)
                   .ule(WorkingArithmetic.Offset.BaseOffset));
    llvm::APInt OffsetInsideArray = WorkingArithmetic.Offset.BaseOffset
                                    - OffsetFromParentArrayElement;
    WorkingArithmetic.Offset.BaseOffset = OffsetInsideArray;

    // If, after adjusting `StartOffset`, the `StartOffset` of `Arithmetic` is
    // still larger than the `Stride` coming from `NAI`, we have to take that
    // into account and add to the `Result` a constant `StridedTerm`
    auto &LC = Result.Offset.LinearCombination;

    // This should never happen by construction
    revng_assert(LC.empty() or LC.back().Stride.ugt(Stride));

    llvm::APInt IndexConstantComponent = llvm::APInt(64, 0);
    if (WorkingArithmetic.Offset.BaseOffset.uge(llvm::APInt(64, Stride))) {
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
      if (llvm::APInt(64, Stride)
            .ult(WorkingArithmetic.Offset.LinearCombination.front().Stride)) {
        return std::nullopt;
      }
      if (Stride == WorkingArithmetic.Offset.LinearCombination.front().Stride) {
        IndexVariableComponent = WorkingArithmetic.Offset.LinearCombination
                                   .front()
                                   .Idx.Variable;
        WorkingArithmetic.Offset.LinearCombination
          .erase(WorkingArithmetic.Offset.LinearCombination.begin());
      }
    }

    // We add a new term to the constructed `LinearCombination`, using the
    // `Index` components identified
    LC.push_back(PointerArithmetic::StridedTerm(llvm::APInt(64, Stride),
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

  auto BasePtrType = Arithmetic.BasePointer.getType().cast<PointerType>();
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
                                            const Traversal &Candidate) {

  // We want to turn an explicit `PointerArithmetic` `PA` in a `Traversal`,
  // assuming that it does the traversal described in `Candidate`
  Traversal Result = Candidate;

  // Because `PA` is explicit (i.e. all array traversals at fixed index have
  // been expanded in the `LinearCombination`), the `Result` `Traversal` will
  // always be the same, except that we have to adjust the leftover offset
  Result.LeftoverOffset = PA.Offset.BaseOffset.getSExtValue()
                          - Candidate.StartOffset;

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
      const Traversal &Candidate = *It;

      // Convert each `ExplicitArithemtic` into a `Traversal`, so we can compare
      // it with `Candidate`. `ExplicitTraversal` is the `Traversal` that we
      // would obtain traversing the `BaseType` with `Explicit` if we did
      // traverse it as the `Candidate` suggests. Basically what can be
      // different is just the `LeftOverOffset`.
      Traversal ExplicitTraversal = toTraversal(Explicit,
                                                PointeeType,
                                                Candidate);

      Score CurrentScore = score(ExplicitTraversal, Candidate);

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
