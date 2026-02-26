#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <optional>
#include <set>

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Casting.h"

#include "mlir/IR/Operation.h"
#include "mlir/IR/Value.h"
#include "mlir/Support/LLVM.h"
#include "mlir/Support/LogicalResult.h"

#include "revng/Clift/Clift.h"
#include "revng/Clift/CliftOpInterfaces.h"
#include "revng/Clift/CliftTypeInterfaces.h"
#include "revng/Clift/CliftTypes.h"
#include "revng/Support/Assert.h"

/// Represents a pointer-typed expression decomposed into a base pointer and an
/// offset expression. The offset is a linear combination of strided terms, which
/// capture array index patterns, plus a constant base offset.
struct PointerArithmetic {

  /// Represents a strided term in the `PointerArithmetic`
  struct StridedTerm {
    llvm::APInt Stride;

    /// We need a `pair` here in order to represent indices with both a constant
    /// and variable component, e.g., `array[i+4]`
    std::pair<mlir::Value, llvm::APInt> Index;

    StridedTerm(llvm::APInt Stride, std::pair<mlir::Value, llvm::APInt> Index) :
      Stride(std::move(Stride)), Index(std::move(Index)) {}
  };

  /// Represents the offset with possible strided terms in the
  /// `PointerArithmetic`
  struct OffsetExpression {
    llvm::APInt BaseOffset; ///< Represents the constant part `Offset`
    llvm::SmallVector<StridedTerm> LinearCombination; ///< Holds the terms of
                                                      ///< the linear
                                                      ///< combination
                                                      ///< components of the
                                                      ///< `Offset`

    OffsetExpression();
    OffsetExpression(llvm::APInt Offset);
  };

  mlir::Value BasePointer; ///< The `BasePointer` relative to the
                           ///< `PointerArithmetic` is expressed
  OffsetExpression Offset; ///< The `Offset` w.r.t. the `BasePointer`

  /// We define a `PointerArithmetic` with an empty `BasePointer` a _numeric_
  bool isNumeric() const;

  /// Check if this is an address (has base pointer) arithmetic
  bool isAddress() const;

  /// Verify the invariants for the strides contained in the PointerArithmetic
  bool verify() const;

  /// Dump method
  void dump() const;
};

/// `PointerArithmetic` computation function entrypoint
std::optional<PointerArithmetic>
computePointerArithmetic(mlir::clift::ExpressionOpInterface PointerToReplace);
