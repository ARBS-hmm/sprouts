module Test
import Main
import Data.SortedMap
import Data.Vect

space1 : Space
space1 = Sn [1,2,3,4,5,6]

node1 = MkNode 1 Edge Borders [2,6] [space1, S0]
node2 = MkNode 2 Edge Borders [1,3] [space1, S0]
node3 = MkNode 3 Edge Borders [2,4] [space1, S0]
node4 = MkNode 4 Edge Borders [3,5] [space1, S0]
node5 = MkNode 5 Edge Borders [4,6] [space1, S0]
node6 = MkNode 6 Sat Borders [1,5,7] [space1, S0]
node7 = MkNode 7 Edge Float [6,8] [space1]
node8 = MkNode 8 Leaf Float [7] [space1]

testGraph : Graph
testGraph = MkGraph nodeMap spaceMap where
  -- Build node map
  nodeMap : SortedMap NodeId Node
  nodeMap = fromList [
    (1, node1),
    (2, node2),
    (3, node3),
    (4, node4),
    (5, node5),
    (6, node6)
  ]
  
  -- Build space map (mapping space IDs to lists of nodes in that space)
  -- Space IDs are just numbers for now
  spaceMap : SortedMap SpaceId (List Node)
  spaceMap = fromList [
    (1, [node1, node2, node3, node4, node5, node6])
  ]

testEnd : Maybe (Node, List NodeId)
testEnd = searchEnd testGraph space1 node8
