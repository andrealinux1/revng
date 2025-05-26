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

/// Implementation class used to run the `MaterializeLoopScopes` transformation
class MaterializeLoopScopesImpl {
  ScopeGraphBuilder SGBuilder;

public:
  MaterializeLoopScopesImpl(Function &F) : SGBuilder(&F) {}

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

                SGBuilder.makeGotoEdge(Predecessor, RegionNode);
              }
            }
          }
        }

        // 2: TODO: handle the exits of each `GenericRegion`
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
