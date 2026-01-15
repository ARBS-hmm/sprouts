module Main

import Data.Fin
import Data.Vect
import Data.SortedMap

data Shape = Free | Leaf | Edge | Sat
data Connection = Float | Borders | Fixed

NodeId = Nat
SpaceId = Nat

Rot : Shape -> Type
Rot Free = () 
Rot Leaf = Vect 1 NodeId
Rot Edge = Vect 2 NodeId
Rot Sat = Vect 3 NodeId

mutual
  data Node : Type where
    MkNode : (id : NodeId) -> 
             (shape : Shape) -> 
             (conn : Connection) -> 
             (rot : Rot shape) -> 
             (spaces : (toFloat conn)) ->
             Node

  data Space : Type where
    S0 : Space
    Sn : List NodeId -> Space

  toFloat : Connection -> Type
  toFloat Float = Vect 1 Space
  toFloat Borders = Vect 2 Space
  toFloat Fixed = Vect 3 Space

nodeId : Node -> NodeId
nodeId (MkNode id shape conn rot spaces) = id

Eq Node where
  (==) (MkNode id _ _ _ _) (MkNode id2 _ _ _ _)= (id == id2) 

Eq Space where
  (==) S0 S0 = True
  (==) (Sn xs) (Sn ys) = (xs == ys) 
  (==) _ _ = False

record Graph where
  constructor MkGraph
  nodeMap : SortedMap NodeId Node
  spaceMap : SortedMap SpaceId (List Node)

conn : Node -> Node -> Connection
conn (MkNode id shape x rot spaces) (MkNode k y z w v) = checkconn x z where
  checkconn : Connection -> Connection -> Connection
  checkconn Float Float = Float
  checkconn Float Borders = Float
  checkconn Float Fixed = Fixed -- impossible /invalid
  checkconn Borders Float = Float -- symmetric
  checkconn Borders Borders = Borders -- or float incase asp is S0 #note
  -- #Pending refactor this logic...not sure how
  checkconn Borders Fixed = Fixed
  checkconn Fixed _ = Fixed

size : SortedMap k v -> Nat
size a = length (Data.SortedMap.toList a)

-- polymorphic List requires case analysis on each case ig
-- or conversion to another single type equivalent to it
spacesToList : {c : Connection} -> toFloat c -> List Space
spacesToList {c = Float} [x] = [x]
spacesToList {c = Borders} [x, y] = [x, y]
spacesToList {c = Fixed} [x, y, z] = [x, y, z]

inSpace : Graph -> Node -> Space -> Bool
inSpace g n sp = 
  let (MkNode id shape conn rot spaces) = n
      spaceList = spacesToList {c=conn} spaces
  in any (== sp) spaceList

findPosition : Eq a => a -> List a -> Maybe Nat
findPosition x [] = Nothing
findPosition x (y :: ys) = 
  if x == y 
    then Just 0
    else case findPosition x ys of
           Just n => Just (S n)
           Nothing => Nothing

safeDrop : Nat -> List a -> List a
safeDrop Z xs = xs
safeDrop (S k) [] = []
safeDrop (S k) (x :: xs) = safeDrop k xs

safeTake : Nat -> List a -> List a
safeTake Z xs = []
safeTake (S k) [] = []
safeTake (S k) (x :: xs) = x :: safeTake k xs

-- deepseek sucks #note
-- end - start ()
diff : Nat -> Nat -> Nat
diff start end = 
  let helper : Nat -> Nat -> Nat
      helper Z end = end
      helper (S k) (S j) = helper k j
      helper (S k) Z = Z  -- Shouldn't happen if start <= end
  in helper start end

getSubsequence : List NodeId -> Nat -> Nat -> List NodeId
getSubsequence nodes start end = 
  let dropped = safeDrop start nodes
      length = S (diff start end)  -- +1 to include both endpoints
  in safeTake length dropped

getComplement : List NodeId -> Nat -> Nat -> List NodeId
getComplement nodes start end =
  let part1 = safeDrop (diff 1 end) nodes -- off by one error**
      part2 = safeTake (start) nodes
  in part1 ++ part2

--test : List NodeId
--test = getComplement [1,2,3,4,5,6,7] 2 5

makeCyclicSpace : List NodeId -> (List NodeId) -> Space
makeCyclicSpace nodes new = Sn (nodes ++ new)

-- #note : deals only with cases where self path isnt considered
getOrderedIndices: List NodeId -> (a,b : NodeId) -> Maybe ((Nat, Nat), Bool)
getOrderedIndices nodes a b = 
  case (findPosition a nodes, findPosition b nodes) of
    (Just i, Just j) => 
      if i == j 
        then Nothing
        else 
          let (start, end) = if i < j then (i, j) else (j, i)
              aIsStart = i < j  -- True if a is at start position
          in Just ((start, end), aIsStart)
    _ => Nothing

connection : Node -> Connection
connection (MkNode id shape conn rot spaces) = conn

getNodeSpaces : Node -> List Space
getNodeSpaces (MkNode _ _ Float rot [space]) = [space]
getNodeSpaces (MkNode _ _ Borders rot [s1, s2]) = [s1, s2]
getNodeSpaces (MkNode _ _ Fixed rot [s1, s2, s3]) = [s1, s2, s3]

getNodesInSpace : Space -> List NodeId
getNodesInSpace S0 = []
getNodesInSpace (Sn ids) = ids

export
dfs : Graph -> Node -> (visited : List NodeId) -> Maybe (List NodeId)
dfs g a visited with (connection a)
  dfs g a visited | Float = 
    let currentId = nodeId a
    in searchFromNode currentId visited
    
  where
    getRotationNeighbors : Node -> List NodeId
    getRotationNeighbors (MkNode _ Free _ () _) = []
    getRotationNeighbors (MkNode _ Leaf _ [x] _) = [x]
    getRotationNeighbors (MkNode _ Edge _ [x,y] _) = [x, y]
    getRotationNeighbors (MkNode _ Sat _ [x,y,z] _) = [x, y, z]
    mutual
      searchFromNode : NodeId -> List NodeId -> Maybe (List NodeId)
      searchFromNode currentId visitedIds =
        if elem currentId visitedIds then
          Nothing  -- Already visited
        else
          case lookup currentId (nodeMap g) of
            Nothing => Nothing  -- Node doesn't exist
            Just node =>
              case connection node of
                -- Found a target node
                Fixed => Just [currentId]
                Borders => Just [currentId]
                -- Float node, search neighbors
                Float => 
                  let newVisited = currentId :: visitedIds
                      neighbors = getRotationNeighbors node
                  in findPath neighbors newVisited currentId
      
      findPath : List NodeId -> List NodeId -> NodeId -> Maybe (List NodeId)
      findPath [] _ _ = Nothing
      findPath (neighborId :: rest) visited currentId =
        if elem neighborId visited then
          findPath rest visited currentId  -- Skip visited
        else
          case searchFromNode neighborId visited of
            Just path => Just (currentId :: path)  -- Success
            Nothing => findPath rest visited currentId
    
  
  dfs g a visited | Borders = Nothing
  dfs g a visited | Fixed = Nothing

-- Helper to get last element of a list
getLast : List a -> Maybe a
getLast [] = Nothing
getLast [x] = Just x
getLast (x :: xs) = getLast xs

export
searchEnd : Graph -> (sp : Space) -> Node -> Maybe (Node, List NodeId)
searchEnd g sp a with (connection a)
  searchEnd g sp a | Float = 
    case dfs g a [] of
      Nothing => Nothing
      Just path =>
        case path of
          -- Need at least 2 elements: start node + at least one other
          (start :: rest) => 
            case getLast rest of
              Nothing => Nothing  -- rest is empty (shouldn't happen)
              Just endpointId =>
                case lookup endpointId (nodeMap g) of
                  Just endpointNode => Just (endpointNode, rest)  -- rest already excludes start
                  Nothing => Nothing
          [] => Nothing  -- Empty path
  
  searchEnd g sp a | Fixed = pure (a, [])
  searchEnd g sp a | Borders = pure (a, [])


export
slice : Graph -> Space -> (a, b : Node) -> (aseq,bseq : List NodeId)-> Maybe (Vect 2 Space)
slice g S0 a b _ _= Nothing
slice g (Sn nodes) a b aseq bseq =
  case getOrderedIndices nodes (nodeId a) (nodeId b) of
    Just ((startIdx, endIdx),True)=> 
      let firstPath = getSubsequence nodes startIdx endIdx
          secondPath = getComplement nodes startIdx endIdx
          newId = size (nodeMap g) + 1
          new = the (List NodeId) (reverse(aseq) ++ [newId] ++ bseq)
          wen = the (List NodeId) (reverse (bseq) ++ [newId] ++ aseq)
          firstSpace = makeCyclicSpace firstPath wen
          secondSpace = makeCyclicSpace secondPath new
      in Just [firstSpace, secondSpace]
    Just ((startIdx,endIdx),False) =>
      let firstPath = getSubsequence nodes startIdx endIdx
          secondPath = getComplement nodes startIdx endIdx
          newId = size (nodeMap g) + 1
          new = the (List NodeId) (reverse(aseq) ++ [newId] ++ bseq)
          wen = the (List NodeId) (reverse (bseq) ++ [newId] ++ aseq)
          firstSpace = makeCyclicSpace firstPath new
          secondSpace = makeCyclicSpace secondPath wen
      in Just [firstSpace, secondSpace]
    Nothing => Nothing

checkForm : Graph -> (asp: Space) -> (a,b:Node) -> Maybe (Vect 2 Space)
checkForm g S0 a b = Nothing
checkForm g asp a b = do
  (aend,aseq) <- searchEnd g asp a
  (bend,bseq) <- searchEnd g asp b
  let condn = ((inSpace g aend asp) && (inSpace g bend asp))
  if condn then (slice g asp aend bend aseq bseq)
           else Nothing

createNewNode : Graph -> (a, b : Node) -> (asp : Space) -> Maybe Node
createNewNode g a b asp = 
  let connectionType = conn a b
  in case connectionType of
       Float => 
         let spacesVect : toFloat Float = [asp]
             aid = nodeId a
             bid = nodeId b
             nid = size(g.nodeMap)+1
             newNode = MkNode nid Edge connectionType [aid,bid] spacesVect
         in Just newNode
       Borders => case checkForm g asp a b of
           Nothing => Nothing
           Just (spaceVect) => 
             let aid = nodeId a
                 bid = nodeId b
                 nid = size(g.nodeMap)+1
                 newNode = MkNode nid Edge Borders [aid,bid] spaceVect
             in pure newNode
       Fixed => Nothing -- impossible case

