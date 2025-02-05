//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/IRBuilder.h"

#include "revng/RestructureCFG/DAGifyPass.h"
#include "revng/RestructureCFG/GenericRegionInfo.h"
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/RestructureCFG/ScopeGraphUtils.h"
#include "revng/Support/Assert.h"
#include "revng/Support/Debug.h"
#include "revng/Support/GraphAlgorithms.h"
#include "revng/Support/IRHelpers.h"

using namespace llvm;

// Debug logger
Logger<> DAGifyPassLogger("dagify");

/// Helper function which transform a retreating edge into a `goto` edge
static void
processRetreating(const revng::detail::FullEdgeDescriptor<BasicBlock *>
                    &Retreating) {
  auto &RetreatingEdge = Retreating.first;
  auto RetreatingIndex = Retreating.second;
  revng_log(DAGifyPassLogger,
            "Found retreating " << RetreatingEdge.first->getName().str()
                                << " , " << RetreatingIndex << " -> "
                                << RetreatingEdge.second->getName().str()
                                << "\n");

  BasicBlock *Source = RetreatingEdge.first;
  BasicBlock *Target = RetreatingEdge.second;
  Function *F = Source->getParent();

  // We should not insert a `goto` in a block already containing a
  // `goto_block` marker
  revng_assert(not isGotoBlock(Source));

  // We are using the `RetreatingIndex`, representing the position of
  // `Target` in the `Source` successors. It must be that `Target` is a
  // successor in the `Terminator` of `Source,` and should not be the
  // additional, optional and unique successor representing the
  // `scope_closer` edge, since we are not able to handle it with the
  // following code. In principle we may support this situation, but we
  // have now an invariant of the `ScopeGraph` which states that
  // `scope_closer` edges should not happen to be retreating edges. This
  // is due to the guarantee we have in how we insert such edges in all
  // the passes of our pipeline.
  Instruction *SourceTerminator = Source->getTerminator();
  revng_assert(RetreatingIndex < SourceTerminator->getNumSuccessors());

  // We create a new block which contains only the `goto`, this is an
  // invariant needed in the `ScopeGraph`
  LLVMContext &Context = getContext(F);
  BasicBlock *GotoBlock = BasicBlock::Create(Context,
                                             "goto_" + Target->getName().str(),
                                             F);

  // Connect the `goto` block with the original target
  IRBuilder<> Builder(Context);
  Builder.SetInsertPoint(GotoBlock);
  Builder.CreateBr(Target);

  // Redirect the `Source`->`Target` to `Source`->`GotoBlock`
  SourceTerminator->setSuccessor(RetreatingIndex, GotoBlock);

  // Insert the `goto_block` marker in the `ScopeGraph`
  ScopeGraphBuilder SGBuilder(F);
  SGBuilder.makeGoto(GotoBlock);
}

char DAGifyPass::ID = 0;

static constexpr const char *Flag = "dagify";
using Reg = llvm::RegisterPass<DAGifyPass>;
static Reg X(Flag, "Perform the DAGify pass on the ScopeGrapgh");

class DAGifyPassImpl {
  Function &F;

public:
  DAGifyPassImpl(Function &F) : F(F) {}

public:
  bool run() {

    // Build the `ScopeGraph` on which the `GenericRegionInfo` analysis should
    // be run
    Function *PF = &F;
    Scope<Function *> ScopeGraph(PF);

    // Build and run the `GenericRegionInfo` analysis on the `ScopeGraph`
    GenericRegionInfo<Scope<Function *>> GRI;
    GRI.clear();
    GRI.compute(ScopeGraph);

    // We keep a boolean variable to track whether the `Module` was modified
    bool ModuleModified = false;

    // We need to perform the DAGify process for each `GenericRegion` that we
    // have identified. We start from the top level `GenericRegion`s, and then
    // we process all the regions nested in a top level one, in a bottom up
    // fashion. Having `GraphTraits` specialized for the tree of
    // `GenericRegion`s, we can handily do this by performing a `post_order`
    // visit on the tree.
    revng_log(DAGifyPassLogger,
              "Running DAGify on function " << F.getName().str() << "\n");

    // We keep a global index of the processed region to easy debug
    size_t RegionIndex = 0;
    for (auto &TopLevelRegion : GRI.top_level_regions()) {
      for (auto *Region : post_order(&TopLevelRegion)) {
        revng_log(DAGifyPassLogger,
                  "DAGify processing region with index: "
                    << std::to_string(RegionIndex) << "\n");

        revng_log(DAGifyPassLogger,
                  "The elected head for this region is block"
                    << Region->getHead()->getName().str() << "\n");

        // Each time we attempt to process a `GenericRegion`, we need to
        // recompute the set of retreating edges, since some of the retreating
        // of a `GenericRegion`, may have been already transformed into `goto`
        // edges during the processing of nested `GenericRegion`s.
        // We collect the retreating edges, performing an exploration that
        // starts from the elected `Head` of each identified `GenericRegion`.
        llvm::SmallPtrSet<BasicBlock *, 4> RegionNodes;
        for (auto &RegionNode : Region->blocks()) {
          RegionNodes.insert(RegionNode);
        }

        BasicBlock *Head = Region->getHead();
        using ScopeGT = GraphTraits<Scope<BasicBlock *>>;
        auto Retreatings = getFullBackedgesWhiteList<BasicBlock *,
                                                     ScopeGT>(Head,
                                                              RegionNodes);

        // Insert a `goto` in place of each retreating edge
        for (auto &Retreating : Retreatings) {

          // As soon as we find a retreating edge, we mark the `Module` as
          // modified
          ModuleModified = true;

          // Process each retreating edge
          processRetreating(Retreating);
        }

        RegionIndex++;
      }
    }

    // Verify that the output `ScopeGraph` is acyclic, after `DAGify` has
    // processed the input, but only when the `VerifyLog` is enabled
    if (VerifyLog.isEnabled()) {
      revng_assert(isDAG(ScopeGraph));
    }

    return ModuleModified;
  }
};

bool DAGifyPass::runOnFunction(llvm::Function &F) {

  // Instantiate and call the `Impl` class
  DAGifyPassImpl DAGifyImpl(F);
  bool FunctionChanged = DAGifyImpl.run();

  // This pass may transform the CFG by transforming some edges into `goto`
  // edges on the `ScopeGraph`. We propagate the information computed by the
  // `Impl` class.
  return FunctionChanged;
}

void DAGifyPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  // This pass does not preserve the CFG
}
