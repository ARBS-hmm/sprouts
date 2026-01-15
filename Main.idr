module Main

import Data.Fin
import Data.Vect
import Data.SortedMap
import Data.List

public export
data Shape = Free | Leaf | Edge | Sat
public export
data Connection = Float | Borders | Fixed

NodeId = Nat
SpaceId = Nat

public export
Rot : Shape -> Type
Rot Free = () 
Rot Leaf = Vect 1 NodeId
Rot Edge = Vect 2 NodeId
Rot Sat = Vect 3 NodeId

mutual
  public export
  data Node : Type where
    MkNode : (id : NodeId) -> 
             (shape : Shape) -> 
             (conn : Connection) -> 
             (rot : Rot shape) -> 
             (spaces : (toFloat conn)) ->
             Node

  public export
  data Space : Type where
    S0 : Space
    Sn : List NodeId -> Space

  public export
  toFloat : Connection -> Type
  toFloat Float = Vect 1 Space
  toFloat Borders = Vect 2 Space
  toFloat Fixed = Vect 3 Space

public export
nodeId : Node -> NodeId
nodeId (MkNode id shape conn rot spaces) = id

Eq Node where
  (==) (MkNode id _ _ _ _) (MkNode id2 _ _ _ _)= (id == id2) 

Eq Space where
  (==) S0 S0 = True
  (==) (Sn xs) (Sn ys) = (xs == ys) 
  (==) _ _ = False

public export
record Graph where
  constructor MkGraph
  nodeMap : SortedMap NodeId Node
  spaceMap : SortedMap SpaceId (List Node)

public export
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

public export
size : SortedMap k v -> Nat
size a = length (Data.SortedMap.toList a)

-- polymorphic List requires case analysis on each case ig
-- or conversion to another single type equivalent to it
public export
spacesToList : {c : Connection} -> toFloat c -> List Space
spacesToList {c = Float} [x] = [x]
spacesToList {c = Borders} [x, y] = [x, y]
spacesToList {c = Fixed} [x, y, z] = [x, y, z]

public export
inSpace : Graph -> Node -> Space -> Bool
inSpace g n sp = 
  let (MkNode id shape conn rot spaces) = n
      spaceList = spacesToList {c=conn} spaces
  in any (== sp) spaceList

public export
findPosition : Eq a => a -> List a -> Maybe Nat
findPosition x [] = Nothing
findPosition x (y :: ys) = 
  if x == y 
    then Just 0
    else case findPosition x ys of
           Just n => Just (S n)
           Nothing => Nothing

public export
safeDrop : Nat -> List a -> List a
safeDrop Z xs = xs
safeDrop (S k) [] = []
safeDrop (S k) (x :: xs) = safeDrop k xs

public export
safeTake : Nat -> List a -> List a
safeTake Z xs = []
safeTake (S k) [] = []
safeTake (S k) (x :: xs) = x :: safeTake k xs

-- deepseek sucks #note
-- end - start ()
public export
diff : Nat -> Nat -> Nat
diff start end = 
  let helper : Nat -> Nat -> Nat
      helper Z end = end
      helper (S k) (S j) = helper k j
      helper (S k) Z = Z  -- Shouldn't happen if start <= end
  in helper start end

public export
getSubsequence : List NodeId -> Nat -> Nat -> List NodeId
getSubsequence nodes start end = 
  let dropped = safeDrop start nodes
      length = S (diff start end)  -- +1 to include both endpoints
  in safeTake length dropped

public export
getComplement : List NodeId -> Nat -> Nat -> List NodeId
getComplement nodes start end =
  let part1 = safeDrop (diff 1 end) nodes -- off by one error**
      part2 = safeTake (start) nodes
  in part1 ++ part2

--test : List NodeId
--test = getComplement [1,2,3,4,5,6,7] 2 5

public export
makeCyclicSpace : List NodeId -> (List NodeId) -> Space
makeCyclicSpace nodes new = Sn (nodes ++ new)

-- #note : deals only with cases where self path isnt considered
public export
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

public export
connection : Node -> Connection
connection (MkNode id shape conn rot spaces) = conn

public export 
shape : Node -> Shape
shape (MkNode id sh conn rot spaces) = sh

public export
getNodeSpaces : Node -> List Space
getNodeSpaces (MkNode _ _ Float rot [space]) = [space]
getNodeSpaces (MkNode _ _ Borders rot [s1, s2]) = [s1, s2]
getNodeSpaces (MkNode _ _ Fixed rot [s1, s2, s3]) = [s1, s2, s3]

public export
getNodesInSpace : Space -> List NodeId
getNodesInSpace S0 = []
getNodesInSpace (Sn ids) = ids

public export
searchEnd : Graph -> (sp : Space) -> Node -> Maybe (Node, List NodeId)
searchEnd g sp a with (connection a, shape a)
  searchEnd g sp a | (Float, Free) = Nothing
  searchEnd g sp a | (Float, Leaf) = ?h
  searchEnd g sp a | (Float, Edge) = ?k
  searchEnd g sp a | (Float, Sat) = ?dfs
  searchEnd g sp a | (Borders,_) = pure (a,[])
  searchEnd g sp a | (Fixed,_) = pure (a,[])
  searchEnd g sp a | (_,_) = Nothing


public export
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

public export
checkForm : Graph -> (asp: Space) -> (a,b:Node) -> Maybe (Vect 2 Space)
checkForm g S0 a b = Nothing
checkForm g asp a b = do
  (aend,aseq) <- searchEnd g asp a
  (bend,bseq) <- searchEnd g asp b
  let condn = ((inSpace g aend asp) && (inSpace g bend asp))
  if condn then (slice g asp aend bend aseq bseq)
           else Nothing

public export
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

