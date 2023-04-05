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

template<class NodeType>
void printEdge(revng::detail::EdgeDescriptor<NodeType *> &Backedge) {
  llvm::dbgs() << "Backedge: ";
  llvm::dbgs() << Backedge.first->getIndex();
  llvm::dbgs() << " -> ";
  llvm::dbgs() << Backedge.second->getIndex();
  llvm::dbgs() << "\n";
}

template<class NodeType>
void printRegion(SmallSetVector<NodeType *> &Region) {
  for (auto *Block : Region) {
    llvm::dbgs() << Block->getIndex() << "\n";
  }
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

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 1);
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

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 2);
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

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    printEdge(Backedge);
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    llvm::dbgs() << "Reachable nodes:\n";
    printRegion(RegionNodes);
    Regions.push_back(std::move(RegionNodes));
  }

  llvm::dbgs() << "\nInitial regions:\n";
  printRegions(Regions);

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  llvm::dbgs() << "\nAfter simplification:\n";
  printRegions(Regions);

  revng_check(Regions.size() == 2);
}
