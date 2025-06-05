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

#include "revng/RestructureCFG/GenericRegionInfo.h"
#include "revng/RestructureCFG/GenericRegionPass.h"
#include "revng/RestructureCFG/MaterializeLoopScopes.h"
#include "revng/RestructureCFG/ScopeGraphAlgorithms.h"
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/Support/Assert.h"

using namespace llvm;

// Debug logger
static Logger<> Log("materialize-loop-scopes");

/// Helper to obtain the immediate postdominator `BasicBlock`, if present
static BasicBlock *
getImmediatePostDominator(BasicBlock *N,
                          PostDomTreeOnView<BasicBlock, Scope> &PostDomTree) {
  auto *Node = PostDomTree.getNode(N)->getIDom();
  if (Node) {
    return Node->getBlock();
  } else {
    return nullptr;
  }
}

// TODO: Verify if we need to run IDS between DAGify and this MLoopScopes pass,
//       or if we can avoid it. If we can avoid, we are happy, because we do not
//       have to deal with keeping the `GenericRegionInfo` information updated
//       across passes that add and delete nodes.

/// Implementation class used to run the `MaterializeLoopScopes` transformation
class MaterializeLoopScopesImpl {
  Function &F;
  ScopeGraphManager<ScopeGraphManagerMode::GenericRegionIDDisabled> SGManager;

public:
  MaterializeLoopScopesImpl(Function &F) : F(F), SGManager(&F) {}

public:
  bool run(const GenericRegionInfo<Scope<Function *>> &RegionInfo) {

    // We keep a boolean variable to track whether the `Function` was modified
    bool FunctionModified = false;

    // We iterate over all the `GenericRegion`s that were found
    for (auto &TopLevelRegion : RegionInfo.top_level_regions()) {
      for (auto *Region : post_order(&TopLevelRegion)) {

        // We create a `SmallSet` for quickly checking if a `Predecessor` is
        // part of the `GenericRegion`
        SmallPtrSet<BasicBlock *, 4> RegionNodes;
        for (auto *RegionNode : Region->blocks()) {
          RegionNodes.insert(RegionNode);
        }

        // 1: In this first step, we handle abnormal entries into each
        //    `GenericRegion`
        revng_log(Log, "Performing late entry normalization\n");

        // Retrieve the elected `Head` of the `GenericRegion`
        BasicBlock *Head = Region->getHead();
        revng_log(Log, "Elected head is: " << Head->getName() << "\n");

        // We want to transform each abnormal entry in a SCS into a `goto` edge
        for (auto *RegionNode : Region->blocks()) {

          // We need to skip elect entry node
          if (RegionNode != Head) {

            // Iterate over the predecessors of each block, and transform in a
            // `goto` edge each abnormal entry
            SmallSetVector<BasicBlock *, 2>
              Predecessors = getScopeGraphPredecessors(RegionNode);
            for (BasicBlock *Predecessor : Predecessors) {
              if (not RegionNodes.contains(Predecessor)) {
                revng_log(Log,
                          "Transforming late entry edge into a goto edge: "
                            << Predecessor->getName() << " -> "
                            << RegionNode->getName() << "\n");

                SGManager.makeGotoEdge(Predecessor, RegionNode);
              }
            }
          }
        }

        dbg << "After late entry normalization:\n";
        llvm::WriteGraph<Scope<llvm::Function *>>(&F,
                                                  "ScopeGraph-" + F.getName());

        // 2: TODO: handle the exits of each `GenericRegion`
        std::optional<BasicBlock *> UniqueSuccessor;

        // TODO: implement the unique successor identification with an assertion
        //       for the base case only (a specific and easily identifiable
        //       successor)
        for (auto *RegionNode : Region->blocks()) {
          SmallSetVector<BasicBlock *, 2>
            Successors = getScopeGraphSuccessors(RegionNode);
          for (BasicBlock *Successor : Successors) {
            if (not RegionNodes.contains(Successor)) {
              revng_assert(not UniqueSuccessor);
              UniqueSuccessor = Successor;
            }
          }
        }

        // TODO: consider pushing the instantiation of the `PostDominatorTree`
        PostDomTreeOnView<BasicBlock, Scope> PostDomTree;
        PostDomTree.recalculate(F);

        // TODO: try and navigate up in the post dominator tree until we find a
        //       node which is outside the current `GenericRegion`
        BasicBlock *Candidate = Head;
        while ((Candidate = getImmediatePostDominator(Candidate,
                                                      PostDomTree))) {
          if (not RegionNodes.contains(Candidate)) {

            // Here we have identified the first node outside the
            // `GenericRegion` which postdominates the entry node. This node
            // will be our candidate for becoming the exit node of the
            // `GenericRegion`.
            UniqueSuccessor = Candidate;
          }
        }

        // TODO: double check that the `UniqueSuccessor` should always exists.
        //
        revng_assert(UniqueSuccessor);

        // Once we have identified the potential `UniqueSuccessor`, we add a
        // `scope_closer` from the entry node of the `GenericRegion` to it
        SGManager.addScopeCloser(Head, *UniqueSuccessor);

        // Logging
        revng_log(Log,
                  "The elected unique successor is: "
                    << (*UniqueSuccessor)->getName() << "\n");
      }
    }

    return FunctionModified;
  }
};

char MaterializeLoopScopes::ID = 0;
static constexpr const char *Flag = "materialize-loop-scopes";
using Reg = llvm::RegisterPass<MaterializeLoopScopes>;
static Reg X(Flag, "Perform the materialization of loop scopes transformation");

bool MaterializeLoopScopes::runOnFunction(llvm::Function &F) {

  // Retrieve the `GenericRegionInfo`
  auto &RegionInfo = getAnalysis<GenericRegionPass>().getResult();

  // Instantiate and call the `Impl` class
  MaterializeLoopScopesImpl IDSImpl(F);
  bool FunctionModified = IDSImpl.run(RegionInfo);

  // This pass may transform the CFG by transforming some edges into `goto`
  // edges, and by adding some `scope_closer` edges on the `ScopeGraph`
  return FunctionModified;
}

void MaterializeLoopScopes::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG

  // This transformation pass consumes the results provided by
  // `GenericRegionPass`
  AU.addRequired<GenericRegionPass>();
}
