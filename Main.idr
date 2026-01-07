module Main

import Data.Vect
import Data.SortedMap

data Shape = Free | Leaf | Edge | Sat
data Connection = Float | Borders | Fixed
data NodeId = MNode Nat
data SpaceId = MSpace Nat


mutual
  data Node : Type where
    MkNode : (id : Nat) -> 
             (shape : Shape) -> 
             (conn : Connection) -> 
             (rot : Rot shape) -> 
             (spaces : toFloat conn) -> 
             Node

  data Space : Type where
    S0 : Space
    Sn : List Node -> Space

  toFloat : Connection -> Type
  toFloat Float = Vect 1 Space
  toFloat Borders = Vect 2 Space
  toFloat Fixed = Vect 3 Space

  Rot : Shape -> Type
  Rot Free = () 
  Rot Leaf = Vect 1 Node
  Rot Edge = Vect 2 Node
  Rot Sat = Vect 3 Node

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

takeList : Nat -> List a -> List a
takeList Z xs = []
takeList (S k) [] = []
takeList (S k) (x :: xs) = x :: takeList k xs

dropList : Nat -> List a -> List a  
dropList Z xs = xs
dropList (S k) [] = []
dropList (S k) (x :: xs) = dropList k xs

createNewNode : (a, b : Node) -> (asp : Space) -> Maybe Node
createNewNode a b asp = 
  let connectionType = conn a b
  in case connectionType of
       Float => 
         let spacesVect : toFloat Float = [asp]
             newNode = MkNode 0 Edge connectionType [a,b] spacesVect
         in Just newNode
       Borders => 
         let spacesVect : toFloat Borders = ?h  -- Need 2 spaces
             newNode = MkNode 0 Edge connectionType [a,b] spacesVect
         in Just newNode
       Fixed => Nothing

