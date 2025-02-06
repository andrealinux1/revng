//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#include "revng/RestructureCFG/DecideWithGotosPass.h"
#include "revng/Support/Debug.h"

using namespace llvm;

// Debug logger
Logger<> DecideWithGotosPassLogger("decide-with-gotos");

char DecideWithGotosPass::ID = 0;

// TODO: review the decision about shortening this flag for a better commandline
//       experience
static constexpr const char *Flag = "decide-with-gotos";
using Reg = llvm::RegisterPass<DecideWithGotosPass>;
static Reg X(Flag, "Perform the DecideWithGotos pass on the ScopeGraph");

bool DecideWithGotosPass::runOnFunction(llvm::Function &F) {
  return true;
}

void DecideWithGotosPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG
}
