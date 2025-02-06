//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#include "revng/RestructureCFG/DecideWithGotosPass.h"
#include "revng/Support/Debug.h"

using namespace llvm;

// Debug logger
Logger<> DecideWithGotosPassLogger("decide-with-gotos");

class DecideWithGotosPassImpl {
  Function &F;

public:
  DecideWithGotosPassImpl(Function &F) : F(F) {}

public:
  bool run() {

    dbg << &F << "\n";

    // We keep a boolean variable to track whether the `Module` was modified
    bool ModuleModified = true;

    return ModuleModified;
  }
};

char DecideWithGotosPass::ID = 0;

// TODO: review the decision about shortening this flag for a better commandline
//       experience
static constexpr const char *Flag = "decide-with-gotos";
using Reg = llvm::RegisterPass<DecideWithGotosPass>;
static Reg X(Flag, "Perform the DecideWithGotos pass on the ScopeGraph");

bool DecideWithGotosPass::runOnFunction(llvm::Function &F) {

  // Instantiate and call the `Impl` class
  DecideWithGotosPassImpl DecideWithGotosImpl(F);
  bool FunctionChanged = DecideWithGotosImpl.run();

  // This pass may transform the CFG by adding some edge into `goto` edges,
  // therefore creating some additional `goto_block`s. We propagate the
  // information computed by the `Impl` class.
  return FunctionChanged;
}

void DecideWithGotosPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG
}
