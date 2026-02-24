//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include "mlir/IR/AsmState.h"
#include "mlir/IR/OperationSupport.h"

#include "revng/Clift/Clift.h"
#include "revng/CliftTransforms/Passes.h"

namespace mlir {
namespace clift {
#define GEN_PASS_DEF_CLIFTDUMPFUNCTION
#include "revng/CliftTransforms/Passes.h.inc"
} // namespace clift
} // namespace mlir

namespace clift = mlir::clift;
using namespace clift;

namespace {

struct DumpFunctionPass : clift::impl::CliftDumpFunctionBase<DumpFunctionPass> {
  void runOnOperation() override {

    clift::FunctionOp Function = getOperation();
    mlir::ModuleOp Module = mlir::cast<mlir::ModuleOp>(Function->getParentOp());

    std::error_code EC;
    llvm::raw_fd_ostream OutputFile(OutputPath + "-"
                                      + Function.getSymName().str(),
                                    EC);
    if (EC) {
      revng_abort(EC.message().c_str());
    }

    mlir::AsmState AsmState(getOperation());
    Module.print(OutputFile, AsmState);
  }
};
} // namespace

clift::PassPtr<clift::FunctionOp> clift::createDumpFunctionPass() {
  return std::make_unique<DumpFunctionPass>();
}
