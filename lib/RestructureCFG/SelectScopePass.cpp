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
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/RestructureCFG/ScopeGraphUtils.h"
#include "revng/RestructureCFG/SelectScopePass.h"
#include "revng/Support/Debug.h"
#include "revng/Support/GraphAlgorithms.h"
#include "revng/Support/IRHelpers.h"

using namespace llvm;

// Debug logger
Logger<> SelectScopePassLogger("select-scope");

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

class SelectScopePassImpl {
  Function &F;

public:
  SelectScopePassImpl(Function &F) : F(F) {}

public:
  bool run() {
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

          // We mark the CFG as modified
          ModuleModified = true;
        }

        Index++;
      }
    }

    // We iterate over the conditional nodes in the `ScopeGraph` in post order
    for (BasicBlock *PONode : llvm::post_order(ScopeGraph)) {
      auto Successors = llvm::children<Scope<BasicBlock *>>(PONode);
      size_t NumSuccessors = std::distance(Successors.begin(),
                                           Successors.end());
      // We skip all the nodes which are not conditional
      if (NumSuccessors <= 1) {
        continue;
      }

      revng_log(SelectScopePassLogger,
                "Processing conditional " << PONode->getName().str() << "\n");

      BasicBlock *PostDominator = PDT[PONode]->getIDom()->getBlock();
      revng_assert(PostDominator);

      revng_log(SelectScopePassLogger,
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

      revng_log(SelectScopePassLogger,
                "Nodes between conditional and its postdominator, in reverse "
                "post order:\n");
      for (auto DFSNode : NodesToProcess) {
        revng_log(SelectScopePassLogger, "  " << DFSNode->getName().str());
      }

      // Initialize the `ReachabilityMap`
      std::map<BasicBlock *, size_t> ReachabilityMap;

      size_t Index = 0;
      for (BasicBlock *ConditionalSuccessor :
           llvm::children<Scope<BasicBlock *>>(PONode)) {

        // Due to the preprocessing that we performed at the beginning, we
        // should never have two edges connecting the same successor of a
        // conditional.
        revng_assert(ReachabilityMap.count(ConditionalSuccessor) == 0);

        // We initialize the `ReachabilityMap` for each `ConditionalSuccessor`
        ReachabilityMap[ConditionalSuccessor] = Index;
        Index++;
      }

      // Process each node in the zone of interest
      for (BasicBlock *Candidate : NodesToProcess) {
        revng_log(SelectScopePassLogger,
                  "Analyzing candidate: " + Candidate->getName().str() << "\n");
        llvm::SmallVector<BasicBlock *> Predecessors;

        // We precompute the predecessors to avoid invalidation due to graph
        // changes. It is fundamental that we always traverse the `ScopeGraph`
        // view of the CFG, or we may end up with some inconsistencies in terms
        // of the visited nodes.
        revng_log(SelectScopePassLogger, "The candidate predecessors are:\n");

        for (auto *Predecessor :
             llvm::children<Inverse<Scope<BasicBlock *>>>(Candidate)) {
          revng_log(SelectScopePassLogger,
                    "  Predecessor: " + Predecessor->getName().str());
          Predecessors.push_back(Predecessor);
        }

        // `Candidate`, could be itself a immediate successor of a conditional
        // node, and therefore correspond to a `ScopeID`. We therefore need to
        // take into consideration it when assigning the final scope for each
        // `Candidate`.
        // We can do this by always enqueuing `Candidate` as a
        // predecessor of itself, this can lead to two situations:
        // 1) `Candidate` is not a successor of the conditional, therefore no
        //    corresponding entry in `ReachabilityMap` will be present, and this
        //    will not influence the decision on the `ScopeID` which will be
        //    finally assigned.
        // 2) `Candidate` is a successor of the conditional, therefore a
        //    corresponding entry in `ReachabilityMap` will be present, and it
        //    will be correctly taken into account for the `ScopeID` decision
        //    process.
        Predecessors.push_back(Candidate);

        // TODO: we elect the first `ScopeID` that we encounter as the elected
        //       `ScopeID`. We may employ a more complex strategy here.
        std::optional<size_t> ElectedScopeID;

        // We process the collected predecessors in reverse order wrt. the order
        // in which they are contained in the `Predecessors` vector. This is
        // important in order to prefer selecting as the elected `ScopeID` the
        // "leftmost" (on a graph visualization) `ScopeID` (and if present, the
        // `ScopeID` corresponding to the `Candidate` node itself, assuming it
        // is a successor of the conditional, MUST be the first processed
        // `ScopeID`, and the elected one).
        for (auto *Predecessor : llvm::reverse(Predecessors)) {
          auto ReachabilityMapIt = ReachabilityMap.find(Predecessor);

          // We may have two situations: 1) There is an entry for `Predecessor`
          // in the `ReachabilityMap`, it means that there is a path connecting
          // the `PONode` conditional and `Candidate`. 2) There is no entry for
          // `Predecessor`, therefore such node wasn't visited during the
          // current exploration of the zone of interest, and therefore it does
          // not lie on any path between the `PONode` conditional and the
          // `Candidate` node.
          if (ReachabilityMapIt != ReachabilityMap.end()) {
            size_t PredecessorScopeID = ReachabilityMapIt->second;

            // If we did not yet elect a `ScopeID`, we elect the current one.
            // Otherwise, we need to transform this edge into a `goto` edge
            if (not ElectedScopeID) {
              ElectedScopeID = PredecessorScopeID;
            } else {
              makeGotoEdge(Predecessor, std::nullopt, Candidate);
              revng_log(SelectScopePassLogger,
                        "Removing predecessor: "
                          + Predecessor->getName().str());

              // We mark the CFG as modified
              ModuleModified = true;
            }
          }
        }

        // We insert in the `ReachabilityMap` a new entry once we assigned the
        // final `ScopeID` to `Candidate`, reflecting the final `ScopeID` that
        // we elected in the above process
        ReachabilityMap[Candidate] = *ElectedScopeID;
      }
    }

    return ModuleModified;
  }
};

char SelectScopePass::ID = 0;
static constexpr const char *Flag = "select-scope";
using Reg = llvm::RegisterPass<SelectScopePass>;
static Reg X(Flag, "Perform the SelectScope pass on the ScopeGraph");

bool SelectScopePass::runOnFunction(llvm::Function &F) {

  // Instantiate and call the `Impl` class
  SelectScopePassImpl SelectScopeImpl(F);
  bool FunctionChanged = SelectScopeImpl.run();

  // This pass may transform the CFG by adding some edge into `goto` edges,
  // therefore creating some additional `goto_block`s. We propagate the
  // information computed by the `Impl` class.
  return FunctionChanged;
}

void SelectScopePass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG
}
