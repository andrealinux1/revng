//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include "mlir/IR/AsmState.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OperationSupport.h"

#include "revng/CliftTransforms/Passes.h"

namespace mlir {
namespace clift {
#define GEN_PASS_DEF_CLIFTDUMPMODULE
#include "revng/CliftTransforms/Passes.h.inc"
} // namespace clift
} // namespace mlir

namespace clift = mlir::clift;
using namespace clift;

namespace {

struct DumpModulePass : clift::impl::CliftDumpModuleBase<DumpModulePass> {
  void runOnOperation() override {

    mlir::ModuleOp Module = getOperation();
    std::error_code EC;
    llvm::raw_fd_ostream OutputFile(OutputPath + "-"
                                      + Module.getSymName()->str(),
                                    EC);
    if (EC) {
      revng_abort(EC.message().c_str());
    }

    mlir::AsmState AsmState(getOperation());
    Module.print(OutputFile, AsmState);
  }
};
} // namespace

clift::PassPtr<mlir::ModuleOp> clift::createDumpModulePass() {
  return std::make_unique<DumpModulePass>();
}
