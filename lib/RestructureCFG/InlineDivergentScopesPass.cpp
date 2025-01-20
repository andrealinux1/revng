//
// Copyright rev.ng Labs Srl. See LICENSE.md for details.
//

#pragma clang optimize off

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/GenericDomTree.h"
#include "llvm/Support/GraphWriter.h"

#include "revng/RestructureCFG/GenericRegionInfo.h"
#include "revng/RestructureCFG/GenericRegionPass.h"
#include "revng/RestructureCFG/InlineDivergentScopesPass.h"
#include "revng/RestructureCFG/ScopeGraphGraphTraits.h"
#include "revng/Support/IRHelpers.h"

using namespace llvm;

// Implementation class used to run the `IDB` transformation
class InlineDivergentScopesImpl {
  llvm::Function &F;

public:
  InlineDivergentScopesImpl(llvm::Function &F) : F(F) {}

public:
  void run() {

    dbg << "HERE\n";

    // 1: Perform the identification of the divergent exits and the divergent
    // branches
    using EdgeDescriptor = revng::detail::EdgeDescriptor<llvm::BasicBlock *>;
    llvm::SmallVector<EdgeDescriptor> DivergentEdges;

    // TODO: remove this: manually add the `C->E` edge in order to test out the
    //       `nullptr` blanketing
    for (BasicBlock &BB : F) {
      for (BasicBlock *Succ : successors(&BB)) {
        if (BB.getName().startswith("block_c")
            and Succ->getName().startswith("block_e")) {
          auto DivergentEdge = EdgeDescriptor(&BB, Succ);
          DivergentEdges.push_back(DivergentEdge);
        }
      }
    }

    // TODO: rewrite the logic to collect the divergent exits

    // TODO: Understand if it is correct to collect all the divergent exits and
    //       then apply the transformation all together, or if it needs to be
    //       interleaved
    // 2: Perform the actual IDB transformation

    // Process all the divergent exits
    for (auto DivergentEdge : DivergentEdges) {

      // Create the new `BasicBlock` representing the conditional inserted by
      // the IDB process
      llvm::BasicBlock *Conditional = DivergentEdge.first;
      llvm::BasicBlock *Successor = DivergentEdge.second;
      llvm::LLVMContext &Context = getContext(Conditional);
      llvm::BasicBlock
        *NewConditional = BasicBlock::Create(Context,
                                             Conditional->getName() + "_idb",
                                             &F);

      // The new conditional will need to operate on the same condition of the
      // original block
      // llvm::Instruction *Terminator = Conditional->getTerminator();
      // llvm::Instruction *ClonedTerminator = Terminator->clone();

      // llvm::IRBuilder<> Builder(NewConditional);
      // Builder.Insert(ClonedTerminator);

      // We need to connect the `NewConditional` to the original successor of
      // the divergent edge

#if 0
      auto ConstantLambda = [&Successor](llvm::BasicBlock *BB) {
        return BB == Successor;
      };
      moveEdgesFromAToB(Conditional, NewConditional, ConstantLambda);
#endif

      moveSuccFromAToB2(Conditional, NewConditional, Successor);
    }

    // TODO: remove this: print the function as debug
    // F.viewCFG();

    // TODO: remove this debug printing, since we are not interested in printing
    //       the content of the body of a `BasicBlock`
#if 1
    for (llvm::BasicBlock &BB : F) {
      dbg << "Block " << BB.getName().str() << " scope graph successors:\n";
      using ScopeGraph = llvm::GraphTraits<Scope<llvm::BasicBlock *>>;
      for (auto Succ = ScopeGraph::child_begin(&BB);
           Succ != ScopeGraph::child_end(&BB);
           ++Succ) {
        dbg << " " << (*Succ)->getName().str() << "\n";
      }
    }
#endif

    // Serialize the `ScopeGraph` for debugging purposes
    llvm::Function *PF = &F;
    Scope<llvm::Function *> ScopeGraph(PF);
    llvm::WriteGraph(ScopeGraph, "ScopeGraph.dot");
  }

  /// Helper function that is used to move a specific outgoing edge `A -> Succ`
  /// in order to become `B -> Succ`. In this first implementation, we don't
  /// clean up the terminator where `Succ` is not reachable anymore, and we rely
  /// on, e.g., `simplifycfg` to take care of that.
  /// TODO: verify that in the situation described above, no simplification in
  ///       turns can lead to inconsistent situations (since the conditional and
  ///       the new cloned conditional created by IDB, need to insist on the
  ///       same condition, and these may become out of sync is IR
  ///       simplifications happens in the middle).
  /// \param A The source basic block.
  /// \param B The target basic block.
  /// \param Succ The successor being moved.
  void moveSuccFromAToB(BasicBlock *A, BasicBlock *B, BasicBlock *Succ) {

    // 1) We remove from the `TerminatorInst` ending `A`, the `Succ`
    //    `BasicBlock`. We do this by substiting `Succ` with `nullptr`. We will
    //    later take care of fixing the `nullptr` occurencies either with the
    //    `simplifycfg` pass or an ulterior custom simplification
    Instruction *TerminatorA = A->getTerminator();
    TerminatorA->replaceSuccessorWith(Succ, nullptr);

    // 2) We redirect all the edges incoming into node `A`, in order to reach
    //    `B` instead

    // We need to save the predecessors, to avoid the invalidation of the
    // iterators
    llvm::SmallVector<BasicBlock *> Predecessors;
    for (BasicBlock *Predecessor : predecessors(A)) {
      Predecessors.push_back(Predecessor);
    }

    for (BasicBlock *Predecessor : Predecessors) {
      Instruction *Terminator = Predecessor->getTerminator();
      Terminator->replaceSuccessorWith(A, B);
    }

    // 3) We also need to connect `B` with `Succ`, with a conditional branch
    //    using the same condition present in `A`
    IRBuilder<> BuilderB(B);
    Instruction *TerminatorB = TerminatorA->clone();
    BuilderB.Insert(TerminatorB);

    // 4) In the cloned `TerminatorB`, we leave alive only the edges reaching
    //    `Succ`
    llvm::SmallVector<BasicBlock *> Successors;
    for (BasicBlock *Successor : successors(B)) {
      if (Successor != Succ) {
        Successors.push_back(Successor);
      }
    }

    for (BasicBlock *Successor : Successors) {
      TerminatorB->replaceSuccessorWith(Successor, nullptr);
    }

    // 5) At this stage, we need to connect `B` to `A`, and we do that by using
    //    the empty slot left by the above substitution
    TerminatorB->replaceSuccessorWith(nullptr, A);
  }

  void moveSuccFromAToB2(BasicBlock *A, BasicBlock *B, BasicBlock *Succ) {

    // TODO: We need to implement the transformation, by reverting what it is done, and by leaving the old living conditional as the first node that is encountered following the execution of the control flow coming from the function entry node

    // TODO: note that the `BasicBlock` `B` has been already created in the caller, even though is empty at this stage. We may need to factor also the creation out here in the new form.

    // We verify that the `BasicBlock` `B` is empty before we start the changes
    // to the LLVMIR
    revng_assert(B->empty());

    // 1) We clone the terminator already present in `BasicBlock` `A`, so that
    //    a superset of the correct successors are already connected
    Instruction *TerminatorA = A->getTerminator();
    Instruction *TerminatorB = TerminatorA->clone();

    IRBuilder<> BuilderB(B);
    BuilderB.Insert(TerminatorB);

    // 2) We remove from the `TerminatorInst` ending `A`, all the edges that do
    //    not target `Succ` (they will be added to the `TerminatorInst` ending
    //    `B`)
    llvm::SmallVector<BasicBlock *> ASuccessors;
    for (BasicBlock *Successor : successors(A)) {
      if (Successor != Succ) {
        ASuccessors.push_back(Successor);
      }
    }

    for (BasicBlock *Successor : ASuccessors) {
      TerminatorA->replaceSuccessorWith(Successor, nullptr);
    }

    // 3) We remove from the `TerminatorInst` ending `B`, all the edges that
    //    target `Succ`, since `Succ` will be reached from `BasicBlock` `A`
    llvm::SmallVector<BasicBlock *> BSuccessors;
    for (BasicBlock *Successor : successors(B)) {
      if (Successor == Succ) {
        BSuccessors.push_back(Successor);
      }
    }

    for (BasicBlock *Successor : BSuccessors) {
      TerminatorB->replaceSuccessorWith(Successor, nullptr);
    }

    // 4) During step 3, we left around some empty slots in the `TerminatorInst`
    //    of `B` (containing a nullptr). Such slots should not be connected to
    //    anything, and therefore we replace it with the first already present
    //    successor. We then rely on `simplifycfg`, or a customly rolled
    //    optimization pass
#if 0
    llvm::BasicBlock *FirstSuccessor;
    for (BasicBlock *Successor : BSuccessors) {
      if (Successor != nullptr) {
        FirstSuccessor = Successor;
      }
    }
    TerminatorB->replaceSuccessorWith(nullptr, FirstSuccessor);
#endif

#if 1
    BasicBlock *FirstSuccessor;
    for (BasicBlock *Successor : successors(B)) {
      if (Successor != nullptr) {
        FirstSuccessor = Successor;
      }
    }
    TerminatorB->replaceSuccessorWith(nullptr, FirstSuccessor);
#endif

    // 5) We connect `BasicBlock` `A` to `BasicBlock` `B` using the first slot
    //    in the `TerminatorInst` of `A` that connected all the other successors
    //    expect `Succ`
    TerminatorA->replaceSuccessorWith(nullptr, B);

    // 6) We add a `ScopeCloser` edge, which connects the divergent part of the
    //    `CFG` with the "main" one, so that a single post dominator tree can be
    //    computed

    // TODO: we rely, for this first implementation, on the assumption that the `ScopeCloser` edge starts from
    Instruction *TerminatorSucc = Succ->getTerminator();
    revng_assert(TerminatorSucc->getNumSuccessors() == 0);

    // We insert the `ScopeCloser` edge at the end of the `Succ` block
    // ScopeCloserMarkerBuilder SCMBuilder(&F);
    // SCMBuilder.setInsertPoint(Succ);
    // SCMBuilder.insertScopeCloserTarget(B);

    ScopeGraphBuilder SGBuilder(&F);
    SGBuilder.addScopeCloser(Succ, B);
  }

  /// Helper function that moves some outgoing edges from basic block A to B.
  /// \param A The source basic block.
  /// \param B The target basic block.
  /// \param shouldMoveEdge A function that decides whether an edge should be
  /// moved based on the successor.
  void moveEdgesFromAToB(BasicBlock *A,
                         BasicBlock *B,
                         std::function<bool(BasicBlock *)> shouldMoveEdge) {
    // Step 1: Get the terminator instruction from A
    Instruction *TerminatorA = A->getTerminator();

    if (!TerminatorA || !TerminatorA->isTerminator()) {
      llvm::errs() << "BasicBlock A does not have a valid terminator!\n";
      return;
    }

    // We will gather all successors we want to move from A to B
    std::vector<BasicBlock *> ToMove;

    for (unsigned I = 0; I < TerminatorA->getNumSuccessors(); ++I) {
      BasicBlock *Succ = TerminatorA->getSuccessor(I);
      if (shouldMoveEdge(Succ)) {
        ToMove.push_back(Succ); // Mark this edge to be moved
      }
    }

    // Step 2: Modify terminator of A to remove the selected successors
    // We need to deal with different terminator types (BranchInst, SwitchInst,
    // etc.)
    if (BranchInst *BI = dyn_cast<BranchInst>(TerminatorA)) {
      if (BI->isConditional()) {
        // If the branch is conditional, we must remove the correct edge
        BasicBlock *ThenBB = BI->getSuccessor(0);
        BasicBlock *ElseBB = BI->getSuccessor(1);

        for (BasicBlock *Succ : ToMove) {
          if (Succ == ThenBB) {
            // Replace the condition so that it branches directly to the ElseBB
            BI->setCondition(ConstantInt::getTrue(BI->getContext()));
            BI->setSuccessor(0, ElseBB); // Set else branch as the only
                                         // successor
          } else if (Succ == ElseBB) {
            BI->setCondition(ConstantInt::getFalse(BI->getContext()));
            BI->setSuccessor(1, ThenBB); // Set then branch as the only
                                         // successor
          }
        }
      } else {
        // For unconditional branches, we simply replace the successor.
        for (BasicBlock *Succ : ToMove) {
          if (BI->getSuccessor(0) == Succ) {
            BI->setSuccessor(0, nullptr);
          }
        }
      }
    } else if (SwitchInst *SI = dyn_cast<SwitchInst>(TerminatorA)) {
      // For SwitchInst, we remove the outgoing edges from A
      for (BasicBlock *Succ : ToMove) {

#if 0
        for (auto Case : SI->cases()) {
          if (Case.getCaseSuccessor() == Succ) {
            SI->removeCase(Case);
          }
        }
#endif

        for (SwitchInst::CaseIt CaseIt = SI->case_begin(),
                                CaseItEnd = SI->case_end();
             CaseIt != CaseItEnd;
             ++CaseIt) {
          if (CaseIt->getCaseSuccessor() == Succ) {
            SI->removeCase(CaseIt);
          }
        }
      }
    }

    // Step 3: Add the successors to B's terminator
    Instruction *TerminatorB = B->getTerminator();
    IRBuilder<> BuilderB(B);

    if (!TerminatorB) {
      // If B does not have a terminator, create a `ret void` by default to
      // start with.
      BuilderB.CreateRetVoid();
      TerminatorB = B->getTerminator();
    }

    // If B has a terminator that supports multiple successors, we modify it.
    if (BranchInst *BI = dyn_cast<BranchInst>(TerminatorB)) {
      if (!BI->isConditional()) {
        // Create a new conditional branch for multiple successors
        BasicBlock *NewSucc = ToMove[0]; // The first successor to move
        for (unsigned i = 1; i < ToMove.size(); ++i) {
          // For each new successor, create a conditional branch to NewSucc or
          // the next successor
          BasicBlock *NextSucc = ToMove[i];
          BI = BuilderB.CreateCondBr(ConstantInt::getTrue(BI->getContext()),
                                     NewSucc,
                                     NextSucc);
          NewSucc = NextSucc;
        }
      }
    } else if (SwitchInst *SI = dyn_cast<SwitchInst>(TerminatorB)) {
      for (BasicBlock *Succ : ToMove) {
#if 1
        // TODO: We should double check that the following `llvm::cast` is
        //       always permitted, and that the `llvm::Type` for the
        //       `SwitchInst` is always a `llvm::ConstantInt`
        SI->addCase(llvm::cast<ConstantInt>(ConstantInt::get(SI->getCondition()
                                                               ->getType(),
                                                             SI->getNumCases()
                                                               + 1)),
                    Succ);
#endif

#if 0
        SI->addCase(ConstantInt::get(SI->getCondition()->getType(),
                                     SI->getNumCases() + 1),
                    Succ);
#endif
      }
    } else {
      // If the terminator of B is not compatible (e.g., `ret void`), we replace
      // it
      TerminatorB->eraseFromParent();
      BuilderB.CreateBr(ToMove[0]);
      // BranchInst *NewBranch = BuilderB.CreateBr(ToMove[0]);

      for (unsigned i = 1; i < ToMove.size(); ++i) {
        BuilderB.CreateBr(ToMove[i]);
      }
    }
  }
};

char InlineDivergentScopesPass::ID = 0;

static constexpr const char *Flag = "ids";
using Reg = llvm::RegisterPass<InlineDivergentScopesPass>;
static Reg X(Flag,
             "Perform the inline of divergent scopes canonicalization process");

bool InlineDivergentScopesPass::runOnFunction(llvm::Function &F) {

  // Instantiate and call the `Impl` class
  InlineDivergentScopesImpl IDSImpl(F);
  IDSImpl.run();

  // This is a pass which can transform the CFG by inserting blocks and
  // redirecting edges, and therefore does not preserve the CFG
  return true;
}

void InlineDivergentScopesPass::getAnalysisUsage(llvm::AnalysisUsage &AU)
  const {

  // We need the information about the computed `GenericRegion`s in order to
  // perform the DAGify operation on the graph
  // TODO: verify this is needed in this step
  AU.addRequired<GenericRegionPass>();
}
