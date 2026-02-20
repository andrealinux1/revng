#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <optional>
#include <variant>

#include "llvm/ADT/APInt.h"
#include "llvm/Support/Casting.h"

#include "mlir/IR/Operation.h"
#include "mlir/IR/Value.h"
#include "mlir/Support/LLVM.h"

#include "revng/Clift/Clift.h"
#include "revng/Clift/CliftOpInterfaces.h"
#include "revng/Clift/CliftTypes.h"
#include "revng/Support/Assert.h"

// Forward declarations
struct PointerArithmetic;
struct Traversal;

void replaceFieldAccess(mlir::clift::ExpressionOpInterface PointerToReplace,
                        const PointerArithmetic &Arithmetic,
                        const Traversal &BestTraversal);
