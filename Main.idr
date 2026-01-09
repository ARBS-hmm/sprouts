module Main

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
             (spaces : (toFloat conn)) -> --Lazy hmm
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
  checkconn Float Fixed = Fixed
  checkconn Borders Float = Float
  checkconn Borders Borders = Borders
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

--Pending
-- supply nearest bounded node to the node
searchEnd : Graph -> (a:Node) -> (sp : Space) -> Maybe Node
searchEnd g a S0 = ?searche_0
searchEnd g a (Sn xs) = ?searche_1


checkForm : Graph -> (a,b,new:Node) -> (asp:Space) -> Maybe (Space,Space)
checkForm g a b new asp = do
  aend <- searchEnd g a asp
  bend <- searchEnd g b asp
  let condn = ((inSpace g aend asp) && (inSpace g bend asp))
  if condn then Nothing -- Pending
           else Nothing

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
  let afterEnd = safeDrop (S end) nodes  -- Drop end+1 elements
      upToStart = safeTake (S start) nodes  -- Take start+1 elements
  in afterEnd ++ upToStart

makeCyclicSpace : List NodeId -> NodeId -> Space
makeCyclicSpace nodes new = Sn (nodes ++ [new])

getOrderedIndices : List NodeId -> (a,b : NodeId) -> Maybe (Nat, Nat)
getOrderedIndices nodes a b = 
  case (findPosition a nodes, findPosition b nodes) of
    (Just i, Just j) => 
      if i == j 
        then Nothing
        else Just (if i < j then (i, j) else (j, i))
    _ => Nothing

isValidSpace : Space -> Bool
isValidSpace S0 = False
isValidSpace (Sn []) = False
isValidSpace (Sn [_]) = False
isValidSpace (Sn _) = True

export
slice : Graph -> Space -> (a,b: Node) -> Maybe (Vect 2 Space)
slice g space a b = 
  if not (isValidSpace space) 
    then Nothing
    else case space of
      Sn nodes => 
        case (getOrderedIndices nodes (nodeId a) (nodeId b)) of
          Just (startIdx, endIdx) => 
            let firstPath = getSubsequence nodes startIdx endIdx
                secondPath = getComplement nodes startIdx endIdx
                newId = size(g.nodeMap) +1
                firstSpace = makeCyclicSpace firstPath newId
                secondSpace = makeCyclicSpace secondPath newId
            in Just [firstSpace, secondSpace]
          Nothing => Nothing
      _ => Nothing

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
       
       Borders => 
         case slice g asp a b of
           Nothing => Nothing
           Just (spaceVect) => 
             let aid = nodeId a
                 bid = nodeId b
                 nid = size(g.nodeMap)+1
                 newNode = MkNode nid Edge Borders [aid,bid] spaceVect
             in Just newNode
       Fixed => Nothing
