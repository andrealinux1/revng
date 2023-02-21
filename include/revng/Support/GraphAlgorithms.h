#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <set>
#include <vector>

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"

#include "revng/Support/Debug.h"

template<typename GT, typename NodeRef = typename GT::NodeRef>
inline llvm::SmallPtrSet<NodeRef, 4>
nodesBetweenImpl(NodeRef Source,
                 NodeRef Destination,
                 const llvm::SmallPtrSetImpl<NodeRef> *IgnoreList) {

  using Iterator = typename GT::ChildIteratorType;
  using NodeSet = llvm::SmallPtrSet<NodeRef, 4>;

  auto HasSuccessors = [](const NodeRef Node) {
    return GT::child_begin(Node) != GT::child_end(Node);
  };

  // Ensure Source has at least one successor
  if (not HasSuccessors(Source)) {
    if (Source == Destination)
      return { Source };
    else
      return {};
  }

  NodeSet Selected = { Destination };
  NodeSet VisitedNodes;

  struct StackEntry {
    StackEntry(NodeRef Node) :
      Node(Node),
      Set({ Node }),
      NextSuccessorIt(GT::child_begin(Node)),
      EndSuccessorIt(GT::child_end(Node)) {}

    NodeRef Node;
    NodeSet Set;
    Iterator NextSuccessorIt;
    Iterator EndSuccessorIt;
  };
  std::vector<StackEntry> Stack;

  Stack.emplace_back(Source);

  while (not Stack.empty()) {
    StackEntry *Entry = &Stack.back();

    NodeRef CurrentSuccessor = *Entry->NextSuccessorIt;

    bool Visited = (VisitedNodes.count(CurrentSuccessor) != 0);
    VisitedNodes.insert(CurrentSuccessor);

    if (Selected.count(CurrentSuccessor) != 0) {

      // We reached a selected node, select all the nodes on the stack
      for (const StackEntry &E : Stack) {
        Selected.insert(E.Set.begin(), E.Set.end());
      }

    } else if (Visited) {
      // We already visited this node, do not proceed in this direction

      auto End = Stack.end();
      auto IsCurrent = [CurrentSuccessor](const StackEntry &E) {
        return E.Set.count(CurrentSuccessor) != 0;
      };
      auto It = std::find_if(Stack.begin(), End, IsCurrent);
      bool IsAlreadyOnStack = It != End;

      if (IsAlreadyOnStack) {
        // It's already on the stack, insert all those on stack until the top
        StackEntry &Target = *It;
        Target.Set.insert(CurrentSuccessor);
        ++It;
        for (const StackEntry &E : llvm::make_range(It, End)) {
          Target.Set.insert(E.Set.begin(), E.Set.end());
        }
      }

    } else if (IgnoreList != nullptr
               and IgnoreList->count(CurrentSuccessor) != 0) {
      // Ignore
    } else {

      // We never visited this node, proceed to its successors, if any
      if (HasSuccessors(CurrentSuccessor)) {
        revng_assert(CurrentSuccessor != nullptr);
        Stack.emplace_back(CurrentSuccessor);
      }

      continue;
    }

    bool TryNext = false;
    do {
      // Move to the next successor
      ++Entry->NextSuccessorIt;

      // Are we done with this entry?
      TryNext = (Entry->NextSuccessorIt == Entry->EndSuccessorIt);

      if (TryNext) {
        // Pop from the stack
        Stack.pop_back();

        // If there's another element process it
        if (Stack.size() == 0) {
          TryNext = false;
        } else {
          Entry = &Stack.back();
        }
      }

    } while (TryNext);
  }

  return Selected;
}

template<class G>
inline llvm::SmallPtrSet<G, 4>
nodesBetween(G Source,
             G Destination,
             const llvm::SmallPtrSetImpl<G> *IgnoreList = nullptr) {
  return nodesBetweenImpl<llvm::GraphTraits<G>>(Source,
                                                Destination,
                                                IgnoreList);
}

template<class G>
inline llvm::SmallPtrSet<G, 4>
nodesBetweenReverse(G Source,
                    G Destination,
                    const llvm::SmallPtrSetImpl<G> *IgnoreList = nullptr) {
  using namespace llvm;
  return nodesBetweenImpl<GraphTraits<Inverse<G>>>(Source,
                                                   Destination,
                                                   IgnoreList);
}

template<typename T>
struct scc_iterator_traits {
  using iterator = llvm::scc_iterator<T, llvm::GraphTraits<T>>;
  using iterator_category = std::forward_iterator_tag;
  using reference = decltype(*llvm::scc_begin((T) nullptr));
  using value_type = std::remove_reference_t<reference>;
  using pointer = value_type *;
  using difference_type = size_t;
};

template<typename NodeTy>
auto exitless_scc_range(NodeTy Entry) {
  using namespace llvm;

  auto Range = make_range(scc_begin(Entry), scc_end(Entry));

  using NodesVector = std::vector<NodeTy>;
  using GT = llvm::GraphTraits<NodeTy>;

  auto Filter = [](const NodesVector &SCC) {
    std::set<NodeTy> SCCNodes;
    SCCNodes.clear();
    for (NodeTy BB : SCC)
      SCCNodes.insert(BB);

    bool HasExit = false;
    bool AtLeastOneEdge = false;
    for (NodeTy BB : SCC) {
      auto Successors = make_range(GT::child_begin(BB), GT::child_end(BB));
      for (NodeTy Successor : Successors) {
        AtLeastOneEdge = true;
        if (SCCNodes.count(Successor) == 0) {
          HasExit = true;
          break;
        }
      }

      if (HasExit)
        break;
    }

    return (not HasExit) and AtLeastOneEdge;
  };

  return make_filter_range(Range, Filter);
}

// clang-format off

/// A generic way to compute a set of entry points to a graph such that any node
/// in said graph is reachable from at least one of those points.
template<typename GraphType>
  requires std::is_pointer_v<GraphType>
std::vector<typename llvm::GraphTraits<GraphType>::NodeRef>
entryPoints(GraphType &&Graph) {
  // clang-format on

  using NodeRef = typename llvm::GraphTraits<GraphType>::NodeRef;

  std::vector<NodeRef> Result;

  // First, find all SCCs reachable from nodes without predecessors
  std::set<const NodeRef> Visited;
  for (const auto &Node : llvm::nodes(Graph)) {
    const auto &Preds = llvm::children<llvm::Inverse<NodeRef>>(Node);
    // If the Node has predecessors, skip it for now. It will be reached by a
    // visit from its predecessor.
    if (Preds.begin() != Preds.end())
      continue;

    // Node has no predecessor, add it to Result.
    Result.push_back(Node);
    // Mark all the nodes reachable from it as Visited.
    for (const auto &Child : llvm::post_order_ext(NodeRef(Node), Visited))
      ;
  }

  // At this point, everything in Visited is reachable from the "easy" entry
  // points, e.g. the nodes without predecessors that we have just detected
  // above.
  for (auto *Node : llvm::nodes(Graph)) {
    if (Visited.contains(Node))
      continue;

    auto SCCBeg = llvm::scc_begin(NodeRef(Node));
    auto SCCEnd = llvm::scc_end(NodeRef(Node));
    // Ignore the case where there are no SCCs.
    if (SCCBeg == SCCEnd)
      continue;

    // Now we look only at the first SCC. We don't want to ever increment the
    // SCC iterator, because we want to only compute one SCC at a time, while
    // incrementing the SCC iterator computes the next SCC, possibly stepping
    // over stuff that has been Visited in the meantime.
    // For an example where this may happen, imagine the graph
    // A->B, B->A, B->C, C->D, D->C, where llvm::nodes visits D before A.
    // When visiting D, it would only see the SCC {C, D}, then when visiting A,
    // it would see the SCC {A, B} first, but it would recompute the SCC {C, D}
    // if incrementing the SCC iterator. This is something we want to avoid.
    const auto &TheSCC = *SCCBeg;
    const NodeRef &SCCEntryNode = TheSCC.front();

    // If the initial node of the SCC is Visited, it means that the whole SCC
    // was visited by one of the previous iterations, so we just ignore it.
    if (Visited.contains(SCCEntryNode))
      continue;

    // Then we mark all the nodes in the SCC as Visited, since we're visiting
    // them now.
    Visited.insert(TheSCC.begin(), TheSCC.end());

    // Now, let's try to figure out if this SCC is reachable from outside.
    // If it is NOT, then we have to add the first element of the SCC to
    // Results.
    bool HasPredecessorOutsideSCC = false;
    for (const NodeRef &SCCNode : TheSCC) {
      for (auto *PredNode : llvm::inverse_children<NodeRef>(SCCNode)) {
        if (llvm::find(TheSCC, PredNode) == TheSCC.end()) {
          HasPredecessorOutsideSCC = true;
          break;
        }
      }
      if (HasPredecessorOutsideSCC)
        break;
    }

    // If no element in TheSCC has a predecessor outside TheSCC we have to elect
    // an entry point for TheSCC. We just pick the first element since we have
    // no better clue about which entry would be best.
    if (not HasPredecessorOutsideSCC)
      Result.push_back(SCCEntryNode);
  }

  return Result;
}

namespace revng::detail {

  template<class NodeT>
  using StatusMap = llvm::DenseMap<NodeT *, bool>;

  template<class NodeT>
  using EdgeDescriptor = std::pair<NodeT *, NodeT *>;

  template<class NodeT>
  class DFState : public StatusMap<NodeT> {
  protected:
    using StatusMap = StatusMap<NodeT>;
    using EdgeDescriptor = EdgeDescriptor<NodeT>;

  protected:
    // Return the insertion iterator on the underlying map.
    std::pair<typename StatusMap::iterator, bool> insertInMap(NodeT *Block) {
      return StatusMap::insert(std::make_pair(Block, true));
    }

    // Return true if b is currently on the active stack of visit.
    bool onStack(NodeT *Block) {
      auto Iter = this->find(Block);
      return Iter != this->end() && Iter->second;
    }

  public:
    // Return the insertion iterator on the underlying map.
    std::pair<typename StatusMap::iterator, bool>
    insertInMapFalse(NodeT *Block) {
      return StatusMap::insert(std::make_pair(Block, false));
    }

  public:
    // Invoked after we have processed all children of a node during the DFS.
    void completed(NodeT *Block) { (*this)[Block] = false; }
  };

  template<class NodeT>
  class DFSBackedgeState : public DFState<NodeT> {
    using typename DFState<NodeT>::StatusMap;
    using typename DFState<NodeT>::EdgeDescriptor;

  private:
    NodeT *CurrentNode = nullptr;
    llvm::SmallSet<EdgeDescriptor, 10> Backedges;
    std::function<bool(NodeT *)> IsValid;

  public:
    DFSBackedgeState(std::function<bool(NodeT *)> IsValid) : IsValid(IsValid) {}

    void setCurrentNode(NodeT *Node) { CurrentNode = Node; }
    llvm::SmallSet<EdgeDescriptor, 10> getBackedges() { return Backedges; }
    std::pair<typename StatusMap::iterator, bool> insert(NodeT *Block) {

      if (IsValid(Block)) {
        // In case we are trying to insert in the `Visited` set a node that is
        // already on the visit stack, we found a backedge.
        if (DFState<NodeT>::onStack(Block)) {
          revng_assert(CurrentNode != nullptr);
          Backedges.insert(std::make_pair(CurrentNode, Block));
        }
        return DFState<NodeT>::insertInMap(Block);
      } else {
        return DFState<NodeT>::insertInMapFalse(Block);
      }
    }
  };

  template<class NodeT>
  class DFSReachableState : public DFState<NodeT> {
    using typename DFState<NodeT>::StatusMap;
    using typename DFState<NodeT>::EdgeDescriptor;

  private:
    // Set which contains the desired targets nodes marked as reachable during
    // the visit.
    llvm::SmallSet<NodeT *, 10> Targets;
    llvm::DenseMap<NodeT *, llvm::SmallSet<NodeT *, 10>> AdditionalNodes;

  public:
    // Insert the initial target node at the beginning of the visit.
    void insertTarget(NodeT *Block) { Targets.insert(Block); }

    llvm::SmallSet<NodeT *, 10> getReachables() { return Targets; }

    llvm::SmallSet<NodeT *, 10> &getAdditional(NodeT *Block) {
      return AdditionalNodes[Block];
    }

    // Customize the `insert` method, in order to add the reachables nodes
    // during the DFS.
    std::pair<typename StatusMap::iterator, bool> insert(NodeT *Block) {

      // Check that, if we are trying to insert a block which is the `Targets`
      // set, we add all the nodes on the current visiting stack in the
      // `Targets` set.
      if (Targets.contains(Block)) {
        for (auto const &[K, V] : *this) {
          if (V) {
            Targets.insert(K);
          }
        }
      }

      // When we encounter a loop, we add to the additional set of nodes the
      // nodes that are onStack, for later additional post-processing.
      if (DFState<NodeT>::onStack(Block)) {
        llvm::SmallSet<NodeT *, 10> &AdditionalSet = AdditionalNodes[Block];
        for (auto const &[K, V] : *this) {
          if (V) {
            AdditionalSet.insert(K);
          }
        }
      }

      // Return the insertion iterator as usual.
      return DFState<NodeT>::insertInMap(Block);
    }
  };

} // namespace revng::detail

template<class NodeT>
llvm::SmallSet<revng::detail::EdgeDescriptor<NodeT>, 10>
getBackedges(NodeT *Block, std::function<bool(NodeT *)> IsValid) {
  revng::detail::DFSBackedgeState<NodeT> State(IsValid);

  // Explore the graph in DFS order and mark backedges.
  for (NodeT *Block : llvm::depth_first_ext(Block, State)) {
    State.setCurrentNode((Block));
  }

  return State.getBackedges();
}

template<class NodeT>
llvm::SmallSet<revng::detail::EdgeDescriptor<NodeT>, 10>
getBackedges(NodeT *Block) {
  std::function<bool(NodeT *)> Lambda = [](NodeT *B) { return true; };
  return getBackedges(Block, Lambda);
}

template<class NodeT>
llvm::SmallSet<NodeT *, 10> nodesBetween(NodeT *Source, NodeT *Target) {
  revng::detail::DFSReachableState<NodeT> State;

  // Initialize the visited set with the target node, which is the boundary
  // that we don't want to trepass when finding reachable nodes.
  State.insertTarget(Target);

  // Explore the graph in DFS order and collect the reachable blocks.
  for (NodeT *Block : llvm::depth_first_ext(Source, State)) {
  }

  auto Targets = State.getReachables();
  // Add in a fixed point fashion the additional nodes.
  llvm::SmallSet<NodeT *, 10> OldTargets;
  do {
    // At each iteration obtain a copy of the old set, so that we are able to
    // exit from the loop as soon no change is made to the `Targets` set.

    OldTargets = Targets;

    // Temporary storage for the nodes to add at each iteration, to avoid
    // invalidation on the `Targets` set.
    llvm::SmallSet<NodeT *, 10> NodesToAdd;

    for (NodeT *Block : Targets) {
      llvm::SmallSet<NodeT *, 10> &AdditionalSet = State.getAdditional(Block);
      NodesToAdd.insert(AdditionalSet.begin(), AdditionalSet.end());
    }

    // Add all the additional nodes found in this step.
    Targets.insert(NodesToAdd.begin(), NodesToAdd.end());
    NodesToAdd.clear();

  } while (Targets != OldTargets);

  return Targets;
}

template<class NodeT>
bool intersect(llvm::SmallSet<NodeT, 10> &First,
               llvm::SmallSet<NodeT, 10> &Second) {
  auto FirstIt = First.begin();
  auto FirstEnd = First.end();
  auto SecondIt = Second.begin();
  auto SecondEnd = Second.end();
  while (FirstIt != FirstEnd and SecondIt != SecondEnd) {
    if (*FirstIt < *SecondIt) {
      ++FirstIt;
    } else {
      if (not(*SecondIt < *FirstIt)) {
        return true; // If we end up here, the elements are equal, hence
                     // intersection is not empty.
      }
      ++SecondIt;
    }
  }

  // If we reach this point no element was in common.
  return false;
}

template<class NodeT>
bool subset(llvm::SmallSet<NodeT, 10> &Contained,
            llvm::SmallSet<NodeT, 10> &Containing) {
  return std::includes(Containing.begin(),
                       Containing.end(),
                       Contained.begin(),
                       Contained.end());
}

template<class NodeT>
bool equal(llvm::SmallSet<NodeT, 10> &First,
           llvm::SmallSet<NodeT, 10> &Second) {
  return First == Second;
}

template<class NodeT>
bool simplifyRegionsStep(llvm::SmallVector<llvm::SmallSet<NodeT, 10>, 10> &R) {
  for (auto RegionIt1 = R.begin(); RegionIt1 != R.end(); RegionIt1++) {
    for (auto RegionIt2 = std::next(RegionIt1); RegionIt2 != R.end();
         RegionIt2++) {
      bool Intersects = intersect(*RegionIt1, *RegionIt2);
      bool IsIncluded = subset(*RegionIt1, *RegionIt2);
      bool IsIncludedReverse = subset(*RegionIt2, *RegionIt1);
      bool AreEquivalent = equal(*RegionIt1, *RegionIt2);
      if (Intersects
          and (((!IsIncluded) and (!IsIncludedReverse)) or AreEquivalent)) {
        (*RegionIt1).insert((*RegionIt2).begin(), (*RegionIt2).end());
        R.erase(RegionIt2);
        return true;
      }
    }
  }

  return false;
}

template<class NodeT>
void simplifyRegions(llvm::SmallVector<llvm::SmallSet<NodeT, 10>, 10> &R) {
  bool Changes = true;
  while (Changes) {
    Changes = simplifyRegionsStep(R);
  }
}

template<class G>
inline llvm::SmallPtrSet<G, 4>
nodesBetween(G Source,
             G Destination,
             const llvm::SmallPtrSetImpl<G> *IgnoreList = nullptr) {
  revng::detail::DFSReachableState<G> State;

  // If the `IgnoreList` is not empty, populate the ext set with the nodes that
  // it contains.
  if (IgnoreList != nullptr) {
    for (G *Element : *IgnoreList) {
      State.insertInMapFalse(Element);
    }
  }

  // Initialize the visited set with the target node, which is the boundary
  // that we don't want to trepass when finding reachable nodes.
  State.insertTarget(Destination);

  // Explore the graph in DFS order and collect the reachable blocks.
  for (G *Block : llvm::depth_first_ext(Source, State)) {
  }

  return State.getReachables();
}
