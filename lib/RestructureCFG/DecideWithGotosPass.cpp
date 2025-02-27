//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/GenericDomTree.h"

#include "revng/ADT/ReversePostOrderTraversal.h"
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

static BasicBlock *makeGotoEdge(BasicBlock *Source,
                                std::optional<size_t> SuccessorIndex,
                                BasicBlock *Target) {

  Function *F = Source->getParent();

  // Create the `goto` block, and connect it with the `Target`
  LLVMContext &Context = getContext(Source);
  BasicBlock *GotoBlock = BasicBlock::Create(Context,
                                             "goto_" + Target->getName().str(),
                                             F);
  IRBuilder<> Builder(Context);
  Builder.SetInsertPoint(GotoBlock);
  Builder.CreateBr(Target);

  // Insert the `goto_block` marker in the `ScopeGraph`
  ScopeGraphBuilder SGBuilder(F);
  SGBuilder.makeGoto(GotoBlock);

  // Redirect the `Source` -> `Target` to `Source` -> `GotoBlock`
  auto SourceTerminator = Source->getTerminator();

  // We use this helper function both to substitute a specific edge connecting
  // `Source` and `Target` (in case of multiple edges between the same pair of
  // nodes), and all the edges connecting `Source` and `Target`. We use the
  // `SuccessorIndex` parameter in order to distinguish between the two
  // situations
  if (SuccessorIndex) {
    SourceTerminator->setSuccessor(*SuccessorIndex, GotoBlock);
  } else {
    SourceTerminator->replaceSuccessorWith(Target, GotoBlock);
  }

  return GotoBlock;
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

    // We compute the `PostDominatorTree` at the beginning of the pass, and we
    // do not update it, as per design, in order not to take into consideration
    // the changing PDT (changes caused by insertion of new exit nodes,
    // represented by the `goto` blocks)
    llvm::PostDomTreeOnView<llvm::BasicBlock, Scope> PDT;
    PDT.recalculate(*PF);
    PDT.print(llvm::dbgs());

    // We preprocess the conditional nodes in order to remove any double edge
    // between a conditional and on of their successor nodes
    for (BasicBlock *PONode : llvm::post_order(ScopeGraph)) {

      auto Successors = llvm::children<Scope<BasicBlock *>>(PONode);
      size_t NumSuccessors = std::distance(Successors.begin(),
                                           Successors.end());
      // We skip all the node which are not conditional nodes
      if (NumSuccessors <= 1) {
        continue;
      }

      llvm::SmallPtrSet<const BasicBlock *, 2> AlreadyConnectedSuccessors;

      // TODO: llvm::enumerate creates a problem with `const`ness
      size_t Index = 0;
      for (BasicBlock *Successor : Successors) {
        if (not AlreadyConnectedSuccessors.contains(Successor)) {

          // It is the first time we encounter `Successor`, therefore we do not
          // need to transform its edge into a `goto`
          AlreadyConnectedSuccessors.insert(Successor);
        } else {
          makeGotoEdge(PONode, Index, Successor);
        }

        Index++;
      }
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

      BasicBlock *PostDominator = PDT[PONode]->getIDom()->getBlock();
      revng_assert(PostDominator);

      revng_log(DecideWithGotosPassLogger,
                "The identified postdominator is "
                  << PostDominator->getName().str() << "\n");

      // We exploit the `Visited` set, by passing it to
      // `ReversePostOrderTraversalExt`, in order to stop the visit at the
      // `PostDominator`
      std::set<BasicBlock *> Visited;
      Visited.insert(PostDominator);

      // We collect all the nodes between the conditional `PONode` and its
      // immediate postdominator, by using the `ReversePostOrderTraversalExt`
      llvm::SmallVector<BasicBlock *> NodesToProcess;
      for (BasicBlock *RPONode :
           ReversePostOrderTraversalExt<Scope<BasicBlock *>>(PONode, Visited)) {
        NodesToProcess.push_back(RPONode);
      }

      // From the collected nodes, we need to remove the first node, which
      // corresponds to the `PONode`, which should not be processed in this
      // round
      revng_assert(NodesToProcess.front() == PONode);
      NodesToProcess.erase(NodesToProcess.begin());

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
                makeGotoEdge(Predecessor, std::nullopt, Candidate);
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
