//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#ifndef MLIR_CLIFT_PASSES
#define MLIR_CLIFT_PASSES

include "mlir/Pass/PassBase.td"
include "mlir/Rewrite/PassUtil.td"

class Clift_Pass<string arg, string operation> : Pass<arg, operation> {
  let dependentDialects = ["clift::CliftDialect"];
}

def CliftLoopDetection : Clift_Pass<"loop-detection", "clift::FunctionOp"> {
  let summary = "Detect Clift loops";
  let constructor = "mlir::clift::createLoopDetectionPass()";
}

def CliftVerifyC : Pass<"verify-c", "mlir::ModuleOp"> {
  let summary = "Verify that the Clift semantics correspond to C semantics " #
                "in the specified target implementation.";
  let constructor = "mlir::clift::createVerifyCPass()";
}

#endif // MLIR_CLIFT_PASSES
