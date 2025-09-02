#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include "mlir/Pass/Pass.h"
#include "revng/mlir/Dialect/Clift/IR/CliftOps.h"

namespace mlir::clift {

template<typename OpT>
using PassPtr = std::unique_ptr<mlir::OperationPass<OpT>>;

#define GEN_PASS_DECL
#include "revng/mlir/Dialect/Clift/Transforms/Passes.h.inc"

PassPtr<clift::FunctionOp> createLoopDetectionPass();

PassPtr<mlir::ModuleOp> createVerifyCPass();

#define GEN_PASS_REGISTRATION
#include "revng/mlir/Dialect/Clift/Transforms/Passes.h.inc"

} // namespace mlir::clift
