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

using namespace llvm;

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

BOOST_AUTO_TEST_CASE(GetBackedgesTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto LG = createLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType>;

  // Compute the backedges set.
  llvm::SmallSet<EdgeDescriptor, 10> Backedges = getBackedges(LG.Entry);

  // Check that the only backedge present.
  revng_check(Backedges.size() == 1);
  EdgeDescriptor Backedge = *Backedges.begin();
  NodeType *Source = Backedge.first;
  NodeType *Target = Backedge.second;
  revng_check(Source == LG.LoopLatch);
  revng_check(Target == LG.Entry);

  // Check the reachability set described by the only backedge present.
  llvm::SmallSet<NodeType *, 10> Reachables = nodesBetween(Target, Source);
  revng_check(Reachables.size() == 2);
  revng_check(Reachables.contains(LG.Entry));
  revng_check(Reachables.contains(LG.LoopLatch));
  revng_check(LG.Entry != LG.LoopLatch);
}

BOOST_AUTO_TEST_CASE(SimplifyRegionsTest) {
  // Create the graph.
  using NodeType = ForwardNode<MyForwardNode>;
  auto OLG = createOLGGraph<NodeType>();
  using EdgeDescriptor = revng::detail::EdgeDescriptor<NodeType>;
  using EdgeSet = llvm::SmallSet<EdgeDescriptor, 10>;
  using BlockSet = llvm::SmallSet<NodeType *, 10>;
  using BlockSetVect = llvm::SmallVector<BlockSet, 10>;

  // Compute the backedges set.
  EdgeSet Backedges = getBackedges(OLG.Entry);
  revng_check(Backedges.size() == 2);

  BlockSetVect Regions;
  for (EdgeDescriptor Backedge : Backedges) {
    BlockSet RegionNodes = nodesBetween(Backedge.second, Backedge.first);
    Regions.push_back(std::move(RegionNodes));
  }

  // Simplify the two regions and verify that they have been collapsed in a
  // single one.
  simplifyRegions(Regions);
  revng_check(Regions.size() == 1);
}
