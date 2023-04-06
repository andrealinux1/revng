/// \file GraphAlgorithms.cpp
/// \brief Test the GraphAlgorithms utils

//
// This file is distributed under the MIT License. See LICENSE.md for details.
//

#define BOOST_TEST_MODULE GraphAlgorithms
bool init_unit_test();
#include "boost/test/unit_test.hpp"

#include "llvm/ADT/SmallSet.h"

#include "revng/ADT/GenericGraph.h"
#include "revng/Support/GraphAlgorithms.h"

struct MyForwardNode {
  MyForwardNode(int Index) : Index(Index) {}
  int Index;
  int getIndex() { return Index; }
};

struct MyBidirectionalNode : MyForwardNode {
  MyBidirectionalNode(int Index) : MyForwardNode(Index) {}
};

template<typename NodeType>
struct LoopGraph {
  using Node = NodeType;
  GenericGraph<Node> Graph;
  Node *Entry;
  Node *LoopLatch;
  Node *Exit;
};

template<typename NodeType>
static LoopGraph<NodeType> createLGGraph() {
  LoopGraph<NodeType> LG;
  auto &Graph = LG.Graph;

  // Create nodes
  LG.Entry = Graph.addNode(1);
  LG.LoopLatch = Graph.addNode(2);
  LG.Exit = Graph.addNode(3);

  // Set entry node
  Graph.setEntryNode(LG.Entry);

  // Create edges
  LG.Entry->addSuccessor(LG.LoopLatch);
  LG.LoopLatch->addSuccessor(LG.Entry);
  LG.Entry->addSuccessor(LG.Exit);

  return LG;
}

template<typename NodeType>
struct OverLappingLoopGraph {
  using Node = NodeType;
  GenericGraph<Node> Graph;
  Node *Entry;
  Node *SecondEntry;
  Node *Latch;
  Node *SecondLatch;
  Node *Exit;
};

template<typename NodeType>
static OverLappingLoopGraph<NodeType> createOLGGraph() {
  OverLappingLoopGraph<NodeType> OLG;
  auto &Graph = OLG.Graph;

  // Create nodes
  OLG.Entry = Graph.addNode(1);
  OLG.SecondEntry = Graph.addNode(2);
  OLG.Latch = Graph.addNode(3);
  OLG.SecondLatch = Graph.addNode(4);
  OLG.Exit = Graph.addNode(5);

  // Create edges
  OLG.Entry->addSuccessor(OLG.SecondEntry);
  OLG.SecondEntry->addSuccessor(OLG.Latch);
  OLG.Latch->addSuccessor(OLG.SecondLatch);
  OLG.Latch->addSuccessor(OLG.Entry);
  OLG.SecondLatch->addSuccessor(OLG.SecondEntry);
  OLG.SecondLatch->addSuccessor(OLG.Exit);

  return OLG;
}

template<typename NodeType>
struct NestedLoopGraph {
  using Node = NodeType;
  GenericGraph<Node> Graph;
  Node *Entry;
  Node *SecondEntry;
  Node *Latch;
  Node *SecondLatch;
  Node *Exit;
};

template<typename NodeType>
static NestedLoopGraph<NodeType> createNLGGraph() {
  NestedLoopGraph<NodeType> NLG;
  auto &Graph = NLG.Graph;

  // Create nodes
  NLG.Entry = Graph.addNode(1);
  NLG.SecondEntry = Graph.addNode(2);
  NLG.Latch = Graph.addNode(3);
  NLG.SecondLatch = Graph.addNode(4);
  NLG.Exit = Graph.addNode(5);

  // Create edges
  NLG.Entry->addSuccessor(NLG.SecondEntry);
  NLG.SecondEntry->addSuccessor(NLG.Latch);
  NLG.Latch->addSuccessor(NLG.SecondLatch);
  NLG.Latch->addSuccessor(NLG.SecondEntry);
  NLG.SecondLatch->addSuccessor(NLG.Entry);
  NLG.SecondLatch->addSuccessor(NLG.Exit);

  return NLG;
}

template<typename NodeType>
static NestedLoopGraph<NodeType> createINLGGraph() {
  NestedLoopGraph<NodeType> INLG = createNLGGraph<NodeType>();
  auto &Graph = INLG.Graph;

  // Create forward inling edge.
  INLG.Entry->addSuccessor(INLG.Latch);
  return INLG;
}

template<typename NodeType>
struct LateEntryLoopGraph {
  using Node = NodeType;
  GenericGraph<Node> Graph;
  Node *Entry;
  Node *LoopHeader;
  Node *LoopLatch;
  Node *Exit;
};

template<typename NodeType>
static LateEntryLoopGraph<NodeType> createLELGGraph() {
  LateEntryLoopGraph<NodeType> LELG;
  auto &Graph = LELG.Graph;

  // Create nodes
  LELG.Entry = Graph.addNode(1);
  LELG.LoopHeader = Graph.addNode(2);
  LELG.LoopLatch = Graph.addNode(3);
  LELG.Exit = Graph.addNode(4);

  // Create edges
  LELG.Entry->addSuccessor(LELG.LoopHeader);
  LELG.LoopHeader->addSuccessor(LELG.LoopLatch);
  LELG.LoopLatch->addSuccessor(LELG.Exit);
  LELG.LoopLatch->addSuccessor(LELG.LoopHeader);
  LELG.Entry->addSuccessor(LELG.LoopLatch);

  return LELG;
}

template<class NodeType>
void printEdge(revng::detail::EdgeDescriptor<NodeType *> &Backedge) {
  llvm::dbgs() << "Backedge: ";
  llvm::dbgs() << Backedge.first->getIndex();
  llvm::dbgs() << " -> ";
  llvm::dbgs() << Backedge.second->getIndex();
  llvm::dbgs() << "\n";
  llvm::dbgs() << "\n";
}

template<class NodeType>
void printRegion(SmallSetVector<NodeType *> &Region) {
  for (auto *Block : Region) {
    llvm::dbgs() << Block->getIndex() << "\n";
  }
  llvm::dbgs() << "\n";
}

template<class NodeType>
void printRegions(llvm::SmallVector<SmallSetVector<NodeType *>> &Rs) {
  using BlockSet = SmallSetVector<NodeType *>;
  size_t RegionIndex = 0;
  for (BlockSet &Region : Rs) {
    llvm::dbgs() << "Region idx: " << RegionIndex << " composed by nodes: \n";
    printRegion(Region);
    RegionIndex++;
  }
  llvm::dbgs() << "\n";
}

template<class MapType>
void printMap(MapType &Map) {
  for (auto const &[K, V] : Map) {
    llvm::dbgs() << "Key: " << K->getIndex() << " Value: " << V << "\n";
  }
  llvm::dbgs() << "\n";
}

BOOST_AUTO_TEST_CASE(GetBackedgesTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto LG = createLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType *>;
  using EdgeSet = SmallSetVector<EdgeDescriptor>;
  using BlockSet = SmallSetVector<NodeType *>;

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(LG.Entry);

  // Check that the only backedge present.
  revng_check(Backedges.size() == 1);
  EdgeDescriptor Backedge = *Backedges.begin();
  NodeType *Source = Backedge.first;
  NodeType *Target = Backedge.second;
  revng_check(Source == LG.LoopLatch);
  revng_check(Target == LG.Entry);

  // Check the reachability set described by the only backedge present.
  BlockSet Reachables = nodesBetween(Target, Source);
  revng_check(Reachables.size() == 2);
  revng_check(Reachables.contains(LG.Entry));
  revng_check(Reachables.contains(LG.LoopLatch));
  revng_check(LG.Entry != LG.LoopLatch);
  revng_check(Reachables[0] == LG.LoopLatch);
  revng_check(Reachables[1] == LG.Entry);
}

BOOST_AUTO_TEST_CASE(SimplifyRegionsTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto OLG = createOLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType *>;
  using EdgeSet = SmallSetVector<EdgeDescriptor>;
  using BlockSet = SmallSetVector<NodeType *>;
  using BlockSetVect = llvm::SmallVector<BlockSet>;

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(OLG.Entry);
  revng_check(Backedges.size() == 2);
  revng_check(Backedges[0].first == OLG.Latch);
  revng_check(Backedges[0].second == OLG.Entry);
  revng_check(Backedges[1].first == OLG.SecondLatch);
  revng_check(Backedges[1].second == OLG.SecondEntry);

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  revng_check(Regions.size() == 2);
  revng_check(Regions[0][0] == OLG.Latch);
  revng_check(Regions[0][1] == OLG.Entry);
  revng_check(Regions[0][2] == OLG.SecondEntry);
  revng_check(Regions[1][0] == OLG.SecondLatch);
  revng_check(Regions[1][1] == OLG.SecondEntry);
  revng_check(Regions[1][2] == OLG.Latch);

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 1);
  revng_check(Regions[0][0] == OLG.Latch);
  revng_check(Regions[0][1] == OLG.Entry);
  revng_check(Regions[0][2] == OLG.SecondEntry);
  revng_check(Regions[0][3] == OLG.SecondLatch);
}

BOOST_AUTO_TEST_CASE(SimplifyNestedRegionsTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto NLG = createNLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType *>;
  using EdgeSet = SmallSetVector<EdgeDescriptor>;
  using BlockSet = SmallSetVector<NodeType *>;
  using BlockSetVect = llvm::SmallVector<BlockSet>;

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(NLG.Entry);
  revng_check(Backedges.size() == 2);
  revng_check(Backedges[0].first == NLG.Latch);
  revng_check(Backedges[0].second == NLG.SecondEntry);
  revng_check(Backedges[1].first == NLG.SecondLatch);
  revng_check(Backedges[1].second == NLG.Entry);

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  revng_check(Regions.size() == 2);
  revng_check(Regions[0][0] == NLG.Latch);
  revng_check(Regions[0][1] == NLG.SecondEntry);
  revng_check(Regions[1][0] == NLG.SecondLatch);
  revng_check(Regions[1][1] == NLG.Entry);
  revng_check(Regions[1][2] == NLG.SecondEntry);
  revng_check(Regions[1][3] == NLG.Latch);

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 2);
  revng_check(Regions[0][0] == NLG.Latch);
  revng_check(Regions[0][1] == NLG.SecondEntry);
  revng_check(Regions[1][0] == NLG.SecondLatch);
  revng_check(Regions[1][1] == NLG.Entry);
  revng_check(Regions[1][2] == NLG.SecondEntry);
  revng_check(Regions[1][3] == NLG.Latch);
}

BOOST_AUTO_TEST_CASE(SimplifyInliningNestedRegionsTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto INLG = createINLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType *>;
  using EdgeSet = SmallSetVector<EdgeDescriptor>;
  using BlockSet = SmallSetVector<NodeType *>;
  using BlockSetVect = llvm::SmallVector<BlockSet>;

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(INLG.Entry);
  revng_check(Backedges.size() == 2);
  revng_check(Backedges[0].first == INLG.Latch);
  revng_check(Backedges[0].second == INLG.SecondEntry);
  revng_check(Backedges[1].first == INLG.SecondLatch);
  revng_check(Backedges[1].second == INLG.Entry);

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  revng_check(Regions.size() == 2);
  revng_check(Regions[0][0] == INLG.Latch);
  revng_check(Regions[0][1] == INLG.SecondEntry);
  revng_check(Regions[1][0] == INLG.SecondLatch);
  revng_check(Regions[1][1] == INLG.Entry);
  revng_check(Regions[1][2] == INLG.SecondEntry);
  revng_check(Regions[1][3] == INLG.Latch);

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 2);
  revng_check(Regions[0][0] == INLG.Latch);
  revng_check(Regions[0][1] == INLG.SecondEntry);
  revng_check(Regions[1][0] == INLG.SecondLatch);
  revng_check(Regions[1][1] == INLG.Entry);
  revng_check(Regions[1][2] == INLG.SecondEntry);
  revng_check(Regions[1][3] == INLG.Latch);
}

BOOST_AUTO_TEST_CASE(LateEntryTest) {
  // Create the graph.
  using NodeType = BidirectionalNode<MyBidirectionalNode>;
  auto LELG = createLELGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType *>;
  using EdgeSet = SmallSetVector<EdgeDescriptor>;
  using BlockSet = SmallSetVector<NodeType *>;
  using BlockSetVect = llvm::SmallVector<BlockSet>;

  llvm::dbgs() << "Current Test:\n";

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(LELG.Entry);
  revng_check(Backedges.size() == 1);
  revng_check(Backedges[0].first == LELG.LoopLatch);
  revng_check(Backedges[0].second == LELG.LoopHeader);

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  // Verify that through the backedge we can reach nodes `2` and `3`.
  BlockSet RegionNodes = Regions[0];
  revng_check(Regions.size() == 1);
  revng_check(RegionNodes[0] == LELG.LoopLatch);
  revng_check(RegionNodes[1] == LELG.LoopHeader);

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Collect the candidate entries for the identified region.
  auto EntryCandidates = getEntryCandidates<NodeType *>(RegionNodes);

  auto EntryCandidatesVector = EntryCandidates.takeVector();
  revng_check(EntryCandidatesVector[0].first == LELG.LoopLatch);
  revng_check(EntryCandidatesVector[0].second == 1);
  revng_check(EntryCandidatesVector[1].first == LELG.LoopHeader);
  revng_check(EntryCandidatesVector[1].second == 1);

  // Compute the Reverse Post Order.
  llvm::SmallVector<NodeType *> RPOT;
  using RPOTraversal = llvm::ReversePostOrderTraversal<NodeType *>;
  llvm::copy(RPOTraversal(LELG.Entry), std::back_inserter(RPOT));

  // Re-compute the entry candidates, since we consumed the map to check for the
  // results.
  EntryCandidates = getEntryCandidates<NodeType *>(RegionNodes);

  // Compute the distance of each node from the entry node.
  auto ShortestPathFromEntry = computeDistanceFromEntry(LELG.Entry);

  // Perform the election of the `Entry` node.
  NodeType *Entry = electEntry<NodeType *>(EntryCandidates,
                                           ShortestPathFromEntry,
                                           RPOT);

  llvm::dbgs() << "Elected entry: " << Entry->getIndex() << "\n";

  // TODO: the entry election currently elects the `LoopLatch` node, but this is
  // suboptimal from an identification point of view. While we insert this unit
  // test now, we should in the future change it in order to identify the
  // `LoopHeader` node as loop entry.
  revng_check(Entry == LELG.LoopLatch);
}
