//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/GenericDomTree.h"

#include "revng/RestructureCFG/DecideWithGotosPass.h"
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/RestructureCFG/ScopeGraphUtils.h"
#include "revng/Support/Debug.h"
#include "revng/Support/GraphAlgorithms.h"
#include "revng/Support/IRHelpers.h"

using namespace llvm;

// Debug logger
Logger<> DecideWithGotosPassLogger("decide-with-gotos");

static bool isReachableOnScopeGraph(BasicBlock *Start, BasicBlock *End) {
  for (BasicBlock *N : llvm::depth_first(Scope<BasicBlock *>(Start))) {
    if (N == End) {

      // As soon as I reach the node I'm looking for, I can early return
      return true;
    }
  }

  // If we didn't reach `End`, we deduce we cannot reach it
  return false;
}

class DecideWithGotosPassImpl {
  Function &F;

public:
  DecideWithGotosPassImpl(Function &F) : F(F) {}

public:
  bool run() {

    // We keep a boolean variable to track whether the `Module` was modified.
    // TODO: assign the initializer to `false`, and reassign it when the first
    //       change is made.
    bool ModuleModified = true;

    Function *PF = &F;
    Scope<Function *> ScopeGraph(PF);

    dbg << "Reverse post order:\n";
    for (BasicBlock *RPONode : llvm::ReversePostOrderTraversal(ScopeGraph)) {
      dbg << RPONode->getName().str() << "\n";
    }

    // We iterate over the conditional nodes in the `ScopeGraph` in post order
    // TODO: verify that processing the conditional nodes in post order is the
    //       legit thing to do
    for (BasicBlock *PONode : llvm::post_order(ScopeGraph)) {

      // TODO: Do we need to take into account the edges on the `ScopeGraph` for
      //       electing the conditional nodes? `goto` edges should not be taken
      //       into account, but what about `scope-closer` edges? Do they count
      //       toward making a node a conditional node? I would say yes but real
      //       motivation?
      auto Successors = llvm::children<Scope<BasicBlock *>>(PONode);
      size_t NumSuccessors = std::distance(Successors.begin(),
                                           Successors.end());
      // We skip all the nodes which are not conditional
      if (NumSuccessors <= 1) {
        continue;
      }

      revng_log(DecideWithGotosPassLogger,
                "Processing conditional " << PONode->getName().str() << "\n");

      // Find the postdominator of `PONode` on the `ScopeGraph`
      llvm::PostDomTreeOnView<llvm::BasicBlock, Scope> PDT;
      PDT.recalculate(*PF);
      PDT.print(llvm::dbgs());

      BasicBlock *PostDominator = PDT[PONode]->getIDom()->getBlock();

      revng_log(DecideWithGotosPassLogger,
                "The identified postdominator is "
                  << PostDominator->getName().str() << "\n");

      // Collect all the nodes between `PONode` and it post dominator
      // auto Nodes = nodesBetween(Scope(PONode), Scope(PostDominator));

      // Collect all the nodes between `PONode` and its post dominator,
      // performing a simple DFS search
      // TODO: confirm that the decision above is indeed the correct thing
      llvm::df_iterator_default_set<BasicBlock *> Visited;
      Visited.insert(PostDominator);
      for (auto *_ :
           llvm::depth_first_ext(Scope<llvm::BasicBlock *>(PONode), Visited)) {
        // We just need to execute this to populate the `Visited` set
        ;
      }

      // We remove the start and end nodes
      Visited.erase(PONode);
      Visited.erase(PostDominator);

      // We now order the nodes following the reverse post order
      // TODO: can we avoid to recompute the reverse post order at each
      //       iteration and just use a global one?
      llvm::SmallVector<BasicBlock *, 4> NodesToProcess;
      for (BasicBlock *RPONode : llvm::ReversePostOrderTraversal(ScopeGraph)) {
        if (Visited.contains(RPONode)) {
          NodesToProcess.push_back(RPONode);
        }
      }

      revng_log(DecideWithGotosPassLogger,
                "Nodes between conditional and its postdominator, in reverse "
                "post order:\n");
      for (auto DFSNode : NodesToProcess) {
        revng_log(DecideWithGotosPassLogger, "  " << DFSNode->getName().str());
      }

      // Process each node
      for (BasicBlock *Candidate : NodesToProcess) {
        llvm::SmallVector<BasicBlock *> PONodeSuccessors;
        for (auto *Successor : llvm::children<Scope<BasicBlock *>>(PONode)) {
          PONodeSuccessors.push_back(Successor);
        }

        // Process `Candidate` to understand if it is undecided wrt. to `PONode`
        size_t Counter = 0;
        llvm::SmallVector<BasicBlock *> ReachingSuccessors;
        for (BasicBlock *PONodeSuccessor : PONodeSuccessors) {
          if (isReachableOnScopeGraph(PONodeSuccessor, Candidate)) {
            ReachingSuccessors.push_back(PONodeSuccessor);
          }
        }

        if (ReachingSuccessors.size() > 1) {

          // It means that a `goto` is needed
          // TODO: here we select the first `PONode` successor as the one non
          //       transformed into `goto`
          for (BasicBlock *Predecessor : predecessors(Candidate)) {
            for (BasicBlock *PONodeSuccessor : skip_front(PONodeSuccessors)) {
              if (isReachableOnScopeGraph(PONodeSuccessor, Predecessor)) {

                auto *PredecessorTerminator = Predecessor->getTerminator();
                LLVMContext &Context = getContext(&F);
                BasicBlock *
                  GotoBlock = BasicBlock::Create(Context,
                                                 "goto_"
                                                   + Candidate->getName().str(),
                                                 &F);

                // Connect the `goto` block with the original target
                IRBuilder<> Builder(Context);
                Builder.SetInsertPoint(GotoBlock);
                Builder.CreateBr(Candidate);

                // Redirect the edge
                PredecessorTerminator->replaceSuccessorWith(Candidate,
                                                            GotoBlock);

                // Insert the `goto_block` marker in the `ScopeGraph`
                ScopeGraphBuilder SGBuilder(&F);
                SGBuilder.makeGoto(GotoBlock);
              }
            }
          }
        }
      }
    }

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
