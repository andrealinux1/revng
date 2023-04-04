#pragma once

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#include <algorithm>
#include <set>
#include <variant>
#include <vector>

#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"

#include "revng/Support/Debug.h"

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
  using StatusMap = llvm::DenseMap<NodeT, bool>;

  template<class NodeT>
  using EdgeDescriptor = std::pair<NodeT, NodeT>;

  template<class NodeT>
  class DFState : public StatusMap<NodeT> {
  protected:
    using StatusMap = StatusMap<NodeT>;
    using EdgeDescriptor = EdgeDescriptor<NodeT>;

  public:
    // Return the insertion iterator on the underlying map.
    std::pair<typename StatusMap::iterator, bool>
    insertInMap(NodeT Block, bool OnStack) {
      return StatusMap::insert(std::make_pair(Block, OnStack));
    }

    // Return true if b is currently on the active stack of visit.
    bool onStack(NodeT Block) {
      auto Iter = this->find(Block);
      return Iter != this->end() && Iter->second;
    }

  public:
    // Invoked after we have processed all children of a node during the DFS.
    void completed(NodeT Block) { (*this)[Block] = false; }
  };

  template<class NodeT>
  class DFSBackedgeState : public DFState<NodeT> {
    using typename DFState<NodeT>::StatusMap;
    using typename DFState<NodeT>::EdgeDescriptor;

  private:
    NodeT CurrentNode = nullptr;
    llvm::SmallSet<EdgeDescriptor, 4> Backedges;
    const std::function<bool(const NodeT)> &IsValid;

  public:
    DFSBackedgeState(const std::function<bool(const NodeT)> &IsValid) :
      IsValid(IsValid) {}

    void setCurrentNode(NodeT Node) { CurrentNode = Node; }
    void insertBackedge(NodeT Source, NodeT Target) {
      Backedges.insert(std::make_pair(Source, Target));
    }
    llvm::SmallSet<EdgeDescriptor, 4> getBackedges() { return Backedges; }
    std::pair<typename StatusMap::iterator, bool> insert(NodeT Block) {

      // If we are trying to insert an invalid block, add it as not on the stack
      // so it does not influence the visit.
      if (IsValid(Block)) {
        return DFState<NodeT>::insertInMap(Block, true);
      } else {

        // We want to completely ignore the fact that we inserted an element in
        // the `DFState`, otherwise we will explore it anyway, therefore we
        // manually return `false`, so the node is not explored at all.
        auto InsertIt = DFState<NodeT>::insertInMap(Block, false);
        return std::make_pair(InsertIt.first, false);
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
    llvm::SmallPtrSet<NodeT, 4> Targets;
    llvm::DenseMap<NodeT, llvm::SmallPtrSet<NodeT, 4>> AdditionalNodes;
    NodeT Source = nullptr;
    NodeT Target = nullptr;
    bool FirstInvocation = true;

  public:
    // Insert the initial target node at the beginning of the visit.
    void insertTarget(NodeT Block) { Targets.insert(Block); }

    // Assign the `Source` node.
    void assignSource(NodeT Block) { Source = Block; }

    // Assign the `Target` node.
    void assignTarget(NodeT Block) { Target = Block; }

    llvm::SmallPtrSet<NodeT, 4> getReachables() { return Targets; }

    llvm::SmallPtrSet<NodeT, 4> &getAdditional(NodeT Block) {
      return AdditionalNodes[Block];
    }

    // Customize the `insert` method, in order to add the reachables nodes
    // during the DFS.
    std::pair<typename StatusMap::iterator, bool> insert(NodeT Block) {

      // We need to insert the `Source` node, which is the first element on
      // which the `insert` method is called, only once, and later on skip it,
      // otherwise we may loop back from the `Source` and add additional nodes.
      revng_assert(Source != nullptr);
      if (!FirstInvocation and Block == Source) {
        return DFState<NodeT>::insertInMap(Block, false);
      }
      FirstInvocation = false;

      // Check that, if we are trying to insert a block which is the `Targets`
      // set, we add all the nodes on the current visiting stack in the
      // `Targets` set.
      auto BeginIt = llvm::GraphTraits<NodeT>::child_begin(Block);
      auto EndIt = llvm::GraphTraits<NodeT>::child_end(Block);
      size_t BlockSuccessorsN = std::distance(BeginIt, EndIt);
      if ((Targets.contains(Block))
          or ((Target == nullptr) && (BlockSuccessorsN == 0))) {
        for (auto const &[K, V] : *this) {
          if (V) {
            Targets.insert(K);
          }
        }
      }

      // When we encounter a loop, we add to the additional set of nodes the
      // nodes that are onStack, for later additional post-processing.
      if (DFState<NodeT>::onStack(Block)) {
        llvm::SmallPtrSet<NodeT, 4> &AdditionalSet = AdditionalNodes[Block];
        for (auto const &[K, V] : *this) {
          if (V) {
            AdditionalSet.insert(K);
          }
        }
      }

      // Return the insertion iterator as usual.
      return DFState<NodeT>::insertInMap(Block, true);
    }
  };

} // namespace revng::detail

template<class GraphT, class GT = llvm::GraphTraits<GraphT>>
llvm::SmallSet<revng::detail::EdgeDescriptor<typename GT::NodeRef>, 4>
getBackedges(GraphT Block,
             const std::function<bool(const typename GT::NodeRef)> &IsValid) {
  using NodeRef = typename GT::NodeRef;
  using StateType = typename revng::detail::DFSBackedgeState<NodeRef>;
  StateType State(IsValid);

  // Declare manually a custom `df_iterator`
  using bdf_iterator = llvm::df_iterator<GraphT, StateType, true, GT>;
  auto Begin = bdf_iterator::begin(Block, State);
  auto End = bdf_iterator::end(Block, State);

  for (NodeRef Block : llvm::make_range(Begin, End)) {
    for (NodeRef Succ :
         llvm::make_range(GT::child_begin(Block), GT::child_end(Block))) {
      if (State.onStack(Succ)) {
        State.insertBackedge(Block, Succ);
      }
    }
  }

  return State.getBackedges();
}

template<class GraphT, class GT = llvm::GraphTraits<GraphT>>
llvm::SmallSet<revng::detail::EdgeDescriptor<typename GT::NodeRef>, 4>
getBackedges(GraphT Block) {
  return getBackedges(Block, [](const typename GT::NodeRef B) { return true; });
}

template<class GraphT, class GT = llvm::GraphTraits<GraphT>>
llvm::SmallPtrSet<typename GT::NodeRef, 4>
nodesBetweenImpl(GraphT Source,
                 GraphT Target,
                 const llvm::SmallPtrSetImpl<GraphT> *IgnoreList = nullptr) {
  using NodeRef = typename GT::NodeRef;
  using StateType = revng::detail::DFSReachableState<NodeRef>;
  StateType State;

  // If the `IgnoreList` is not empty, populate the ext set with the nodes that
  // it contains.
  if (IgnoreList != nullptr) {
    for (GraphT Element : *IgnoreList) {
      State.insertInMap(Element, false);
    }
  }

  // Assign the `Source` node.
  State.assignSource(Source);

  // Initialize the visited set with the target node, which is the boundary
  // that we don't want to trepass when finding reachable nodes.
  State.assignTarget(Target);
  State.insertTarget(Target);
  State.insertInMap(Target, false);

  using nbdf_iterator = llvm::df_iterator<GraphT, StateType, true, GT>;
  auto Begin = nbdf_iterator::begin(Source, State);
  auto End = nbdf_iterator::end(Source, State);

  for (NodeRef Block : llvm::make_range(Begin, End)) {
    (void) Block;
  }

  auto Targets = State.getReachables();
  // Add in a fixed point fashion the additional nodes.
  llvm::SmallPtrSet<NodeRef, 4> OldTargets;
  do {
    // At each iteration obtain a copy of the old set, so that we are able to
    // exit from the loop as soon no change is made to the `Targets` set.

    OldTargets = Targets;

    // Temporary storage for the nodes to add at each iteration, to avoid
    // invalidation on the `Targets` set.
    llvm::SmallPtrSet<NodeRef, 4> NodesToAdd;

    for (NodeRef Block : Targets) {
      llvm::SmallPtrSet<NodeRef, 4> &AdditionalSet = State.getAdditional(Block);
      NodesToAdd.insert(AdditionalSet.begin(), AdditionalSet.end());
    }

    // Add all the additional nodes found in this step.
    Targets.insert(NodesToAdd.begin(), NodesToAdd.end());
    NodesToAdd.clear();

  } while (Targets != OldTargets);

  return Targets;
}

template<class GraphT>
inline llvm::SmallPtrSet<GraphT, 4>
nodesBetween(GraphT Source,
             GraphT Destination,
             const llvm::SmallPtrSetImpl<GraphT> *IgnoreList = nullptr) {
  return nodesBetweenImpl<GraphT, llvm::GraphTraits<GraphT>>(Source,
                                                             Destination,
                                                             IgnoreList);
}

template<class GraphT>
inline llvm::SmallPtrSet<GraphT, 4>
nodesBetweenReverse(GraphT Source,
                    GraphT Destination,
                    const llvm::SmallPtrSetImpl<GraphT> *IgnoreList = nullptr) {
  using namespace llvm;
  return nodesBetweenImpl<GraphT, GraphTraits<Inverse<GraphT>>>(Source,
                                                                Destination,
                                                                IgnoreList);
}

template<class NodeT>
bool intersect(llvm::SmallPtrSet<NodeT, 4> &First,
               llvm::SmallPtrSet<NodeT, 4> &Second) {

  std::set<NodeT> FirstSet;
  std::set<NodeT> SecondSet;
  FirstSet.insert(First.begin(), First.end());
  SecondSet.insert(Second.begin(), Second.end());

  llvm::SmallVector<NodeT> Intersection;
  std::set_intersection(FirstSet.begin(),
                        FirstSet.end(),
                        SecondSet.begin(),
                        SecondSet.end(),
                        std::back_inserter(Intersection));
  return !Intersection.empty();
}

template<class NodeT>
bool subset(llvm::SmallPtrSet<NodeT, 4> &Contained,
            llvm::SmallPtrSet<NodeT, 4> &Containing) {
  std::set<NodeT> ContainedSet;
  std::set<NodeT> ContainingSet;
  ContainedSet.insert(Contained.begin(), Contained.end());
  ContainingSet.insert(Containing.begin(), Containing.end());
  return std::includes(ContainingSet.begin(),
                       ContainingSet.end(),
                       ContainedSet.begin(),
                       ContainedSet.end());
}

template<class NodeT>
bool equal(llvm::SmallPtrSet<NodeT, 4> &First,
           llvm::SmallPtrSet<NodeT, 4> &Second) {
  std::set<NodeT> FirstSet;
  std::set<NodeT> SecondSet;
  FirstSet.insert(First.begin(), First.end());
  SecondSet.insert(Second.begin(), Second.end());
  return FirstSet == SecondSet;
}

template<class NodeT>
bool simplifyRegionsStep(llvm::SmallVector<llvm::SmallPtrSet<NodeT, 4>> &R) {
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
void simplifyRegions(llvm::SmallVector<llvm::SmallPtrSet<NodeT, 4>> &Rs) {
  bool Changes = true;
  while (Changes) {
    Changes = simplifyRegionsStep(Rs);
  }
}

// Reorder the vector containing the regions so that they are in increasing size
// order.
template<class NodeT>
void sortRegions(llvm::SmallVector<llvm::SmallPtrSet<NodeT, 4>> &Rs) {
  std::sort(Rs.begin(),
            Rs.end(),
            [](llvm::SmallPtrSet<NodeT, 4> &First,
               llvm::SmallPtrSet<NodeT, 4> &Second) {
              return First.size() < Second.size();
            });
}

template<class GraphT,
         class GT = llvm::GraphTraits<GraphT>,
         typename NodeRef = typename GT::NodeRef>
llvm::DenseMap<NodeRef, size_t> computeDistanceFromEntry(GraphT Source) {
  llvm::DenseMap<NodeRef, size_t> ShortestPathFromEntry;

  using SetType = llvm::bf_iterator_default_set<NodeRef>;
  using bf_iterator = llvm::bf_iterator<GraphT, SetType, GT>;
  auto BFSIt = bf_iterator::begin(Source);
  auto BFSEnd = bf_iterator::end(Source);

  for (; BFSIt != BFSEnd; ++BFSIt) {
    NodeRef Block = *BFSIt;
    size_t Depth = BFSIt.getLevel();

    // Obtain the insertion iterator for the `Depth` block element.
    auto ShortestIt = ShortestPathFromEntry.insert({ Block, Depth });

    // If we already had in the map an entry for the current block, we need to
    // revng_assert that the previously found value for the `Depth` is less or
    // equal
    // of the `Depth` we are inserting.
    if (ShortestIt.second == false) {
      revng_assert(ShortestIt.first->second <= Depth);
    }
  }

  return ShortestPathFromEntry;
}

template<class NodeT>
bool setContains(llvm::SmallPtrSetImpl<NodeT> &Set, NodeT &Element) {
  return Set.contains(Element);
}

template<class GraphT, class GT = llvm::GraphTraits<GraphT>>
auto child_range(GraphT Block) {
  return llvm::make_range(GT::child_begin(Block), GT::child_end(Block));
}

template<class GraphT>
auto successor_range(GraphT Block) {
  return child_range(Block);
}

template<class GraphT>
auto predecessor_range(GraphT Block) {
  return child_range<GraphT, llvm::GraphTraits<llvm::Inverse<GraphT>>>(Block);
}

template<class NodeRef>
llvm::DenseMap<NodeRef, size_t>
getEntryCandidates(llvm::SmallPtrSetImpl<NodeRef> &Region) {

  // `DenseMap` that will contain all the candidate entries of a region, with
  // the associated incoming edges degree.
  llvm::DenseMap<NodeRef, size_t> Result;

  // We can iterate over all the predecessors of a block, if we find a pred not
  // in the current set, we increment the counter of the entry edges.
  for (NodeRef Block : Region) {
    for (NodeRef Predecessor : predecessor_range(Block)) {
      if (not setContains(Region, Predecessor)) {
        Result[Block]++;
      }
    }
  }

  return Result;
}

template<class NodeT>
size_t mapAt(llvm::DenseMap<NodeT, size_t> &Map, NodeT Element) {
  auto MapIt = Map.find(Element);
  revng_assert(MapIt != Map.end());
  return MapIt->second;
}

template<class NodeT>
NodeT electEntry(llvm::DenseMap<NodeT, size_t> &EntryCandidates,
                 llvm::DenseMap<NodeT, size_t> &ShortestPathFromEntry,
                 llvm::SmallVectorImpl<NodeT> &RPOT) {
  // Elect the Entry as the the candidate entry with the largest number of
  // incoming edges from outside the region.
  // If there's a tie, i.e. there are 2 or more candidate entries with the
  // same number of incoming edges from an outer region, we select the entry
  // with the minimal shortest path from entry.
  // It it's still a tie, i.e. there are 2 or more candidate entries with the
  // same number of incoming edges from an outer region and the same minimal
  // shortest path from entry, then we disambiguate by picking the entry that
  // comes first in RPOT.
  NodeT Entry = Entry = EntryCandidates.begin()->first;
  {
    size_t MaxNEntries = EntryCandidates.begin()->second;
    auto ShortestPathIt = ShortestPathFromEntry.find(Entry);
    revng_assert(ShortestPathIt != ShortestPathFromEntry.end());
    size_t ShortestPath = mapAt(ShortestPathFromEntry, Entry);
    auto EntriesEnd = EntryCandidates.end();
    for (NodeT Block : RPOT) {
      auto EntriesIt = EntryCandidates.find(Block);
      if (EntriesIt != EntriesEnd) {
        const auto &[EntryCandidate, NumIncoming] = *EntriesIt;
        if (NumIncoming > MaxNEntries) {
          Entry = EntryCandidate;
          ShortestPath = mapAt(ShortestPathFromEntry, EntryCandidate);
        } else if (NumIncoming == MaxNEntries) {
          size_t SP = mapAt(ShortestPathFromEntry, EntryCandidate);
          if (SP < ShortestPath) {
            Entry = EntryCandidate;
            ShortestPath = SP;
          }
        }
      }
    }
  }
  revng_assert(Entry != nullptr);
  return Entry;
}

template<class NodeRef>
llvm::SmallVector<std::pair<NodeRef, NodeRef>>
getOutlinedEntries(llvm::DenseMap<NodeRef, size_t> &EntryCandidates,
                   llvm::SmallPtrSetImpl<NodeRef> &Region,
                   NodeRef Entry) {
  llvm::SmallVector<std::pair<NodeRef, NodeRef>> LateEntryPairs;
  for (const auto &[Other, NumIncoming] : EntryCandidates) {
    if (Other != Entry) {
      llvm::SmallVector<NodeRef> OutsidePredecessor;
      for (NodeRef Predecessor : predecessor_range(Other)) {
        if (not setContains(Region, Predecessor)) {
          OutsidePredecessor.push_back(Predecessor);
          LateEntryPairs.push_back({ Predecessor, Other });
        }
      }
      revng_assert(OutsidePredecessor.size() == NumIncoming);
    }
  }

  return LateEntryPairs;
}

template<class NodeRef>
llvm::SmallVector<std::pair<NodeRef, NodeRef>>
getExitNodePairs(llvm::SmallPtrSetImpl<NodeRef> &Region) {

  // Vector that contains the pairs of exit/successor node pairs.
  llvm::SmallVector<std::pair<NodeRef, NodeRef>> ExitSuccessorPairs;

  // We iterate over all the successors of a block, if we find a successor not
  // in the current set, we add the pairs of node to the set.
  for (NodeRef Block : Region) {
    for (NodeRef Successor : successor_range(Block)) {
      if (not setContains(Region, Successor)) {
        ExitSuccessorPairs.push_back({ Block, Successor });
      }
    }
  }

  return ExitSuccessorPairs;
}

template<class NodeRef>
llvm::SmallVector<std::pair<NodeRef, NodeRef>>
getPredecessorNodePairs(NodeRef Node) {
  llvm::SmallVector<std::pair<NodeRef, NodeRef>> PredecessorNodePairs;
  for (NodeRef Predecessor : predecessor_range(Node)) {
    PredecessorNodePairs.push_back({ Predecessor, Node });
  }

  return PredecessorNodePairs;
}

template<class NodeRef>
llvm::SmallVector<std::pair<NodeRef, NodeRef>>
getLoopPredecessorNodePairs(NodeRef Node,
                            llvm::SmallPtrSetImpl<NodeRef> &Region) {
  llvm::SmallVector<std::pair<NodeRef, NodeRef>> LoopPredecessorNodePairs;
  for (NodeRef Predecessor : predecessor_range(Node)) {
    if (not setContains(Region, Predecessor)) {
      LoopPredecessorNodePairs.push_back({ Predecessor, Node });
    }
  }

  return LoopPredecessorNodePairs;
}

template<class NodeRef>
llvm::SmallVector<std::pair<NodeRef, NodeRef>>
getContinueNodePairs(NodeRef Entry,
                     llvm::SmallPtrSetImpl<NodeRef> &Region,
                     NodeRef IgnoredNode) {
  llvm::SmallVector<std::pair<NodeRef, NodeRef>> ContinueNodePairs;
  for (NodeRef Predecessor : predecessor_range(Entry)) {
    if (Predecessor != IgnoredNode and setContains(Region, Predecessor)) {
      ContinueNodePairs.push_back({ Predecessor, Entry });
    }
  }

  return ContinueNodePairs;
}

namespace revng::detail {

template<class NodeT>
class RegionTree;

template<class NodeT>
class RegionNode {
public:
  using BlockNode = NodeT;

  struct ChildRegionDescriptor {
    size_t ChildIndex;
    RegionTree<NodeT> *OwningRegionTree;
  };

private:
  using links_container = llvm::SmallVector<BlockNode>;
  using links_iterator = typename links_container::iterator;
  using links_const_iterator = typename links_container::const_iterator;
  using links_range = llvm::iterator_range<links_iterator>;
  using links_const_range = llvm::iterator_range<links_const_iterator>;

  RegionTree<NodeT> &OwningRegionTree;

  using getPointerT = RegionNode *(*) (ChildRegionDescriptor &);
  using getConstPointerT =
    const RegionNode *(*) (const ChildRegionDescriptor &);

  static RegionNode *getPointer(ChildRegionDescriptor &Successor) {
    RegionTree<NodeT> *OwningRegionTree = Successor.OwningRegionTree;
    size_t ChildIndex = Successor.ChildIndex;
    RegionNode *ChildRegionPointer = &OwningRegionTree->getRegion(ChildIndex);
    revng_assert(ChildRegionPointer != nullptr);
    return ChildRegionPointer;
  }

  static_assert(std::is_same_v<decltype(&getPointer), getPointerT>);

  static const RegionNode *
  getConstPointer(const ChildRegionDescriptor &Successor) {
    RegionTree<NodeT> *OwningRegionTree = Successor.OwningRegionTree;
    size_t ChildIndex = Successor.ChildIndex;
    RegionNode *ChildRegionPointer = &OwningRegionTree->getRegion(ChildIndex);
    revng_assert(ChildRegionPointer != nullptr);
    return ChildRegionPointer;
  }

  static_assert(std::is_same_v<decltype(&getConstPointer), getConstPointerT>);

  using succ_container = llvm::SmallVector<ChildRegionDescriptor>;
  using succ_naked_it = typename succ_container::iterator;
  using succ_naked_const_it = typename succ_container::const_iterator;
  using succ_naked_range = llvm::iterator_range<succ_naked_it>;
  using succ_naked_const_range = llvm::iterator_range<succ_naked_const_it>;
  using succ_iterator = llvm::mapped_iterator<succ_naked_it, getPointerT>;
  using succ_const_iterator = llvm::mapped_iterator<succ_naked_const_it,
                                                    getConstPointerT>;
  using succ_range = llvm::iterator_range<succ_iterator>;
  using succ_const_range = llvm::iterator_range<succ_const_iterator>;

  enum EntryState { Invalid, NodesVector, ChildrenVector };

private:
  void erase(links_container &V, BlockNode Value) {
    V.erase(std::remove(V.begin(), V.end(), Value), V.end());
  }

  void erase(succ_container &V, ChildRegionDescriptor Value) {
    V.erase(std::remove(V.begin(), V.end(), Value), V.end());
  }

private:
  links_container Nodes;
  succ_container Children;
  EntryState EntryState = Invalid;

public:
  RegionNode(RegionTree<NodeT> &RegionTree) : OwningRegionTree(RegionTree) {}

  RegionNode(const RegionNode &) = default;
  RegionNode(RegionNode &&) = default;
  RegionNode &operator=(const RegionNode &) = default;
  RegionNode &operator=(RegionNode &&) = default;

  links_iterator begin() { return Nodes.begin(); }
  links_const_iterator begin() const { return Nodes.begin(); }
  links_iterator end() { return Nodes.end(); }
  links_const_iterator end() const { return Nodes.end(); }
  links_range blocks() { return llvm::make_range(begin(), end()); }
  links_const_range blocks() const { return llvm::make_range(begin(), end()); }

  llvm::SmallSet<NodeT, 4> getBlocksSet() {
    llvm::SmallSet<NodeT, 4> BlocksSet;
    for (NodeT Block : blocks()) {
      BlocksSet.insert(Block);
    }

    return BlocksSet;
  }

  succ_naked_it succ_begin_naked() { return Children.begin(); }
  succ_naked_it succ_end_naked() { return Children.end(); }
  succ_naked_const_it succ_const_begin_naked() { return Children.begin(); }
  succ_naked_const_it succ_const_end_naked() { return Children.end(); }
  succ_naked_range successor_range_naked() {
    return llvm::make_range(succ_begin_naked(), succ_end_naked());
  }
  succ_naked_const_range successor_const_range_naked() {
    return llvm::make_range(succ_const_begin_naked(), succ_const_end_naked());
  }

  // If we invoke this method, the entry node must be a block node, so no
  // substitution with a child region descriptor must have happened.
  NodeT getEntryBlock() {
    revng_assert(EntryState == NodesVector);
    revng_assert(!Nodes.empty());
    return Nodes[0];
  }

  std::optional<NodeT> getEntryIfBlock() {
    if (EntryState == NodesVector) {
      revng_assert(!Nodes.empty());
      return Nodes[0];
    }
    return std::nullopt;
  }

  std::variant<NodeT, ChildRegionDescriptor *> getEntry() {
    revng_assert(EntryState != Invalid);
    if (EntryState == NodesVector) {
      revng_assert(!Nodes.empty());
      return Nodes[0];
    } else if (EntryState == ChildrenVector) {
      revng_assert(!Children.empty());
      return &Children[0];
    }
    __builtin_unreachable();
  }

  succ_iterator succ_begin() {
    return llvm::map_iterator(Children.begin(), getPointer);
  }
  succ_const_iterator succ_const_begin() const {
    return llvm::map_iterator(Children.begin(), getConstPointer);
  }
  succ_iterator succ_end() {
    return llvm::map_iterator(Children.end(), getPointer);
  }
  succ_const_iterator succ_const_end() const {
    return llvm::map_iterator(Children.end(), getConstPointer);
  }
  succ_range successor_range() {
    return llvm::make_range(succ_begin(), succ_end());
  }
  succ_const_range successor_const_range() {
    return llvm::make_range(succ_const_begin(), succ_const_end());
  }

  // Insert helpers.
  void insertElement(BlockNode Element) { Nodes.push_back(Element); }
  void insertElement(size_t Element) {
    struct ChildRegionDescriptor ElementDescriptor = { Element,
                                                       &OwningRegionTree };
    Children.push_back(ElementDescriptor);
  }

  void insertElementEntry(BlockNode Element) {
    Nodes.insert(begin(), Element);
    EntryState = NodesVector;
  }
  void insertElementEntry(size_t Element) {
    struct ChildRegionDescriptor ElementDescriptor = { Element,
                                                       &OwningRegionTree };
    Children.insert(succ_begin_naked(), ElementDescriptor);
    EntryState = ChildrenVector;
  }

  // If we are removing the first element (of either the `Nodes` or `Children`
  // vector), we signal it with the return code.
  bool eraseElement(BlockNode Element) {
    bool IsEntry = (Nodes.front() == Element) and (EntryState == NodesVector);
    erase(Nodes, Element);
    return IsEntry;
  }

  bool eraseElement(ChildRegionDescriptor Element) {
    bool IsEntry = (Children.front() == Element)
                   and (EntryState == ChildrenVector);
    erase(Children, Element);
    return IsEntry;
  }

  bool isChildRegionEntry(RegionNode *ChildRegion) {

    // The `ChildRegion` can be the entry, only if the entry block is indeed an
    // index to a `ChildRegion`, and the first region in the `Children` vector
    // is indeedthe passed one.
    revng_assert(!Children.empty());
    if (EntryState == ChildrenVector) {
      ChildRegionDescriptor &Entry = Children[0];
      if (&Entry.OwningRegionTree->getRegion(Entry.ChildIndex) == ChildRegion) {
        return true;
      }
    }
    return false;
  }

  bool containsBlock(const BlockNode Candidate) {
    llvm::SmallVector<RegionNode *> ToAnalyze;
    ToAnalyze.push_back(this);

    while (!ToAnalyze.empty()) {
      RegionNode *LastRegion = ToAnalyze.back();
      ToAnalyze.pop_back();

      // Insert all the element in the currently analyzed region in a set to
      // check for the containement criteria.
      llvm::SmallSet<BlockNode, 4> RegionSet;
      for (BlockNode Element : *LastRegion) {
        RegionSet.insert(Element);
      }

      // Finish comparison if we find the node in the current `RegionSet`.
      if (RegionSet.contains(Candidate)) {
        return true;
      }

      // Enqueue all the children regions.
      for (RegionNode *ChildRegion : LastRegion->successor_range()) {
        ToAnalyze.push_back(ChildRegion);
      }
    }

    // If the exploration of all the nested regions did not find the node, we
    // can return false.
    return false;
  }

  llvm::SmallVector<BlockNode> getAllNestedBlocks() {
    llvm::SmallVector<RegionNode *> ToAnalyze;
    ToAnalyze.push_back(this);

    llvm::SmallVector<BlockNode> Result;

    while (!ToAnalyze.empty()) {
      RegionNode *LastRegion = ToAnalyze.back();
      ToAnalyze.pop_back();

      for (BlockNode Element : *LastRegion) {
        Result.push_back(Element);
      }

      for (RegionNode *ChildRegion : LastRegion->successor_range()) {
        ToAnalyze.push_back(ChildRegion);
      }
    }

    return Result;
  }

  llvm::DenseMap<BlockNode, size_t>
  getEntryCandidates(RegionNode *ParentRegion) {

    // `DenseMap` that will contain all the candidate entries of the current
    // region, with the associated incoming edges degree.
    llvm::DenseMap<BlockNode, size_t> Result;

    // We iterate over all the predecessors of a block, if we find a predecessor
    // not in the current region, but which is in the parent region, we
    // increment the counter of the entry edges.
    // We need to explicitly look in the parent region only, because in
    // principle we could have a late entry pointing in a region nested
    // arbitrarly in other regions. In this way, we outline the iteration only
    // when the `ParentRegion` is indeed the region from where the late entry
    // edge is departing from.
    for (BlockNode Block : getAllNestedBlocks()) {
      for (BlockNode Predecessor : predecessor_range(Block)) {
        if (not containsBlock(Predecessor)
            and ParentRegion->containsBlock(Predecessor)) {
          Result[Block]++;
        }
      }
    }

    return Result;
  }

  llvm::SmallVector<std::pair<BlockNode, BlockNode>>
  getOutlinedEntries(llvm::DenseMap<BlockNode, size_t> &EntryCandidates,
                     BlockNode Entry,
                     RegionNode *ParentRegion) {
    llvm::SmallVector<std::pair<BlockNode, BlockNode>> LateEntryPairs;
    for (const auto &[Other, NumIncoming] : EntryCandidates) {
      if (Other != Entry) {
        llvm::SmallVector<BlockNode> OutsidePredecessor;
        for (BlockNode Predecessor : predecessor_range(Other)) {
          if (not containsBlock(Predecessor)) {
            OutsidePredecessor.push_back(Predecessor);
            LateEntryPairs.push_back({ Predecessor, Other });
          }
        }
        revng_assert(OutsidePredecessor.size() == NumIncoming);
      }
    }

    return LateEntryPairs;
  }
};

template<class NodeT>
class RegionTree {
  using RegionVector = RegionNode<NodeT>;

public:
  using links_container = llvm::SmallVector<RegionVector>;
  using links_it = typename links_container::iterator;
  using links_const_it = typename links_container::const_iterator;
  using links_rev_it = typename links_container::reverse_iterator;
  using links_const_rev_it = typename links_container::const_reverse_iterator;
  using links_range = llvm::iterator_range<links_it>;
  using links_rev_range = llvm::iterator_range<links_rev_it>;
  using links_const_range = llvm::iterator_range<links_const_it>;
  using links_const_rev_range = llvm::iterator_range<links_const_rev_it>;

private:
  links_container Regions;

public:
  RegionTree() = default;

  void clear() { Regions.clear(); }

  void insertRegion(RegionVector &&Region) {
    Regions.emplace_back(std::move(Region));
  }

  RegionVector &front() { return Regions.front(); }

  links_it begin() { return Regions.begin(); }
  links_const_it begin() const { return Regions.begin(); }
  links_it end() { return Regions.end(); }
  links_const_it end() const { return Regions.end(); }
  links_range regions() { return llvm::make_range(begin(), end()); }
  links_const_range regions() const { return llvm::make_range(begin(), end()); }

  links_rev_it rbegin() { return Regions.rbegin(); }
  links_const_rev_it rbegin() const { return Regions.rbegin(); }
  links_rev_it rend() { return Regions.rend(); }
  links_const_rev_it rend() const { return Regions.rend(); }
  links_rev_range reverseRegions() {
    return llvm::make_range(rbegin(), rend());
  }
  links_const_rev_range reverseRegions() const {
    return llvm::make_range(rbegin(), rend());
  }

  RegionVector &getRegion(size_t Index) { return Regions[Index]; }
};

using ParentMap = llvm::DenseMap<std::ptrdiff_t, std::ptrdiff_t>;

template<class NodeT>
class ParentTree {
  using ParentMap = llvm::DenseMap<std::ptrdiff_t, std::ptrdiff_t>;
  using RegionSet = llvm::SmallPtrSet<NodeT, 4>;

  using links_container = llvm::SmallVector<RegionSet>;
  using links_iterator = typename links_container::iterator;
  using links_const_iterator = typename links_container::const_iterator;
  using links_range = llvm::iterator_range<links_iterator>;
  using links_const_range = llvm::iterator_range<links_const_iterator>;

private:
  ParentMap Map;
  links_container Rs;
  llvm::DenseMap<std::ptrdiff_t, bool> IsRootRegionMap;
  llvm::DenseMap<std::ptrdiff_t, NodeT> EntryMap;
  bool ReadyState = false;

private:
  RegionSet &getRegionFromIndex(std::ptrdiff_t Index) { return Rs[Index]; }

  void computeParents() {
    for (auto RegionIt1 = Rs.begin(); RegionIt1 != Rs.end(); RegionIt1++) {
      for (auto RegionIt2 = std::next(RegionIt1); RegionIt2 != Rs.end();
           RegionIt2++) {
        if (subset(*RegionIt1, *RegionIt2)) {
          Map[getRegionIndex(*RegionIt1)] = getRegionIndex(*RegionIt2);
          break;
        }
      }
    }
  }

  std::ptrdiff_t getRegionIndex(RegionSet &Region) {
    for (auto RegionIt = Rs.begin(); RegionIt != Rs.end(); RegionIt++) {
      if (*RegionIt == Region) {
        return std::distance(Rs.begin(), RegionIt);
      }
    }

    // TODO: We may want to soft fail in this situation, if we allow to query
    //       the data structure with no assurance that the intended region is
    //       present.
    revng_abort();
  }

  void computePartialOrder() {
    links_container OrderedRegions;
    llvm::SmallPtrSet<size_t, 4> Processed;

    while (Rs.size() != Processed.size()) {
      for (auto RegionIt1 = begin(); RegionIt1 != end(); RegionIt1++) {
        if (Processed.count(getRegionIndex(*RegionIt1)) == 0) {
          bool FoundParent = false;
          for (auto RegionIt2 = std::next(RegionIt1); RegionIt2 != Rs.end();
               RegionIt2++) {
            if (Processed.count(getRegionIndex(*RegionIt2)) == 0) {
              if (getParent(*RegionIt1) == *RegionIt2) {
                FoundParent = true;
                break;
              }
            }
          }

          if (FoundParent == false) {
            OrderedRegions.push_back(*RegionIt1);
            Processed.insert(getRegionIndex(*RegionIt1));
            break;
          }
        }
      }
    }

    // Swap the region vector with the ordered one.
    std::reverse(OrderedRegions.begin(), OrderedRegions.end());
    Rs.swap(OrderedRegions);
  }

  links_iterator begin() { return Rs.begin(); }
  links_const_iterator begin() const { return Rs.begin(); }
  links_iterator end() { return Rs.end(); }
  links_const_iterator end() const { return Rs.end(); }

public:
  ParentTree() = default;

  void clear() {
    Map.clear();
    Rs.clear();
    IsRootRegionMap.clear();
    EntryMap.clear();
    ReadyState = false;
  }

  links_container &getRegions() {
    revng_assert(ReadyState);
    return Rs;
  }

  // TODO: we need this method because we cannot have `std::optional` with
  //       references, and therefore we need a method to check that the
  //       `getParent` will not fail (not being possible to return an
  //       `optional`, and checking the results user side).
  bool hasParent(RegionSet &Child) {
    revng_assert(ReadyState);

    std::ptrdiff_t ChildIndex = getRegionIndex(Child);
    auto MapIt = Map.find(ChildIndex);
    return MapIt != Map.end();
  }

  RegionSet &getParent(RegionSet &Child) {
    std::ptrdiff_t ChildIndex = getRegionIndex(Child);
    auto MapIt = Map.find(ChildIndex);
    revng_assert(MapIt != Map.end());
    std::ptrdiff_t ParentIndex = MapIt->second;
    RegionSet &Parent = getRegionFromIndex(ParentIndex);
    return Parent;
  }

  void insertRegion(RegionSet &Region) { Rs.emplace_back(std::move(Region)); }

  void order() {
    computeParents();
    computePartialOrder();
    computeParents();

    // Flag the `ParentTree` as ready to use, so we do not use incidentally
    // before it has been order and it is considered ready to use.
    ReadyState = true;
  }

  links_range regions() {
    revng_assert(ReadyState);
    return llvm::make_range(begin(), end());
  }
  links_const_range regions() const {
    revng_assert(ReadyState);
    return llvm::make_range(begin(), end());
  }

  void setRegionRoot(RegionSet &Region, bool Value) {
    revng_assert(ReadyState);
    std::ptrdiff_t RegionIndex = getRegionIndex(Region);
    IsRootRegionMap[RegionIndex] = Value;
  }

  bool isRegionRoot(RegionSet &Region) {
    revng_assert(ReadyState);

    std::ptrdiff_t RegionIndex = getRegionIndex(Region);
    auto MapIt = IsRootRegionMap.find(RegionIndex);
    revng_assert(MapIt != IsRootRegionMap.end());
    return MapIt->second;
  }

  void setRegionEntry(RegionSet &Region, NodeT Entry) {
    revng_assert(ReadyState);

    std::ptrdiff_t RegionIndex = getRegionIndex(Region);
    EntryMap[RegionIndex] = Entry;
  }

  NodeT getRegionEntry(RegionSet &Region) {
    revng_assert(ReadyState);

    std::ptrdiff_t RegionIndex = getRegionIndex(Region);
    auto MapIt = EntryMap.find(RegionIndex);
    revng_assert(MapIt != EntryMap.end());
    return MapIt->second;
  }
};

} // namespace revng::detail
