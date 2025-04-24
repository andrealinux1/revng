//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/GenericDomTree.h"

#include "revng/RestructureCFG/MaterializeLoopScopes.h"
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/RestructureCFG/ScopeGraphUtils.h"
#include "revng/Support/Assert.h"
#include "revng/Support/GraphAlgorithms.h"
#include "revng/Support/IRHelpers.h"

using namespace llvm;

/// Implementation class used to run the `MaterializeLoopScopes` transformation
class MaterializeLoopScopesImpl {
  Function &F;
  ScopeGraphBuilder SGBuilder;

public:
  MaterializeLoopScopesImpl(Function &F) : F(F), SGBuilder(&F) {}

public:
  bool run() {

    // We keep a boolean variable to track whether the `Function` was modified
    bool FunctionModified = false;

    dbg << &F << "\n";

    return FunctionModified;
  }
};

char MaterializeLoopScopes::ID = 0;
static constexpr const char *Flag = "materialize-loop-scopes";
using Reg = llvm::RegisterPass<MaterializeLoopScopes>;
static Reg X(Flag, "Perform the materialization of loop scopes transformation");

bool MaterializeLoopScopes::runOnFunction(llvm::Function &F) {

  // Instantiate and call the `Impl` class
  MaterializeLoopScopesImpl IDSImpl(F);
  bool FunctionModified = IDSImpl.run();

  // This pass may transform the CFG by transforming some edges into `goto`
  // edges, and by adding some `scope_closer` edges on the `ScopeGraph`
  return FunctionModified;
}

void MaterializeLoopScopes::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG
}
