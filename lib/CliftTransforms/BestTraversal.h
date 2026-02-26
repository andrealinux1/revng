#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <optional>
#include <set>
#include <vector>

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"

#include "mlir/IR/Operation.h"
#include "mlir/IR/Value.h"
#include "mlir/Support/LLVM.h"

#include "revng/Clift/Clift.h"
#include "revng/Clift/CliftOpInterfaces.h"
#include "revng/Clift/CliftTypes.h"
#include "revng/Support/Assert.h"

// Forward declarations
struct PointerArithmetic;

/// `NestedArrayShape` represents the shape of a nested array element within a
/// type traversal, including its offset from the parent array element, the
/// number of elements, and the stride between consecutive elements.
struct NestedArrayShape {

  // Represents the offset from the last _parent array_ element traversed to
  // reach this array
  int64_t OffsetFromParentArrayElement;
  uint64_t NumElements;
  uint64_t Stride;
};

/// A path of traversed `array`s is represented as a vector. These are kept
/// sorted with larger strides first, and we assume that there are no duplicated
/// strides
using ArrayPath = std::vector<NestedArrayShape>;

/// The `ArrayShape` struct is used to represent a generic array shape, where
/// the concrete accessed element is not taken into consideration
struct ArrayShape {
  uint64_t NumElements; ///< Size of the described array
  uint64_t Stride; ///< Stride of the described array

  /// Orders `ArrayShape`s by descending `Stride`, then ascending `NumElements`
  bool operator<(const ArrayShape &Other) const;

  bool operator==(const ArrayShape &Other) const = default;
};

/// This represents a type traversal starting from a fixed `BaseType`.
/// A Traversal represents a way to traverse `BaseType` accessing struct fields,
/// union fields and array elements, to reach a given fixed total offset from
/// the beginning of `BaseType`. The total offset is composed of two components:
///
/// * The `StartOffset`, which is the start offset of the innermost nested
/// target field that the traversal reaches
/// * The `LeftoverOffset`, which is the additional offset inside that target
/// field, not explicitly captured by the `Traversal`.
///
/// Note: The index of the traversal for an array is not specified.
///       In this sense, the traversal is "abstract".
/// Note: `StartOffset` behaves like if the first element of each
///       array is always traversed.
struct Traversal {

  /// The nested type, inside `BaseType`, where the `Traversal` lands
  mlir::Type TargetType;

  /// The start offset, from a fixed `BaseType`, which is "consumed" by this
  /// `Traversal`
  int64_t StartOffset;

  /// Additional offset inside the `TargetType`, not explicitly covered by the
  /// `Traversal`
  int64_t LeftoverOffset;

  /// The ID/Offset of each traversed `union`/`struct` field
  std::vector<uint32_t> TraversedFields;

  /// This sorted set contains the `ArrayShape` describing the array traversals,
  /// ordered in descending order by `Stride` size (operator `<` on the
  /// `ArrayShape`). There can be consecutive `ArrayShape` with the same
  /// `Stride`, to allow to express e.g., `int array[1][1]`.
  std::set<ArrayShape> TraversedArrays;

  /// Total depth described by this `Traversal` (fields + array elements)
  long depth() const;

  /// Initial offset accessed by the `Traversal`
  int64_t begin() const;

  /// First out of bound offset accessed by the `Traversal`, considering the
  /// size of the `PointeeType`
  int64_t end() const;

  /// Helper method to obtain all the `Stride`s described by the `Traversal`,
  /// useful for
  std::set<uint64_t> getStrides() const;

  /// Helper method used to identify an empty `Traversal` (a `Traversal` which
  /// does not involve any traversed struct field or array)
  bool empty() const;

  /// Debug `dump` method used to provide a textual representation on the logger
  /// of the `Traversal`
  void dump() const;
};

/// `TraversalInfo` describes a set of `Traversal`s and `ArrayPaths`, which we
/// associated to a `mlir::Type` (so we can cache them)
struct TraversalInfo {
  std::vector<Traversal> Traversals;
  std::vector<ArrayPath> ArrayPaths;
};

/// The map used to cache the `Traversal`s and `ArrayPath`s computed starting
/// from a `mlir::Type`
using TraversalInfoMap = llvm::DenseMap<mlir::Type, TraversalInfo>;

/// Main entry point used to compute the `BestTraversal` from an `Expression`
/// and PointerArithmetic`.
std::optional<Traversal>
computeBestTraversal(mlir::clift::ExpressionOpInterface PointerToReplace,
                     const PointerArithmetic &Arithmetic,
                     TraversalInfoMap &Data);
