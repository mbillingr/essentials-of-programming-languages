data BinTree = Nil | Node Int BinTree BinTree

data PathNode = Left Int BinTree
                | Right Int BinTree

data NavTree = NNil (List PathNode)
             | Nav Int BinTree BinTree (List PathNode)


binTreeToNavTree : BinTree -> (List PathNode) -> NavTree
binTreeToNavTree [] = NNil
binTreeToNavTree (Node x l r) = Nav x l r

navTreeToBinTree : NavTree -> BinTree
navTreeToBinTree (NNil _) = []
navTreeToBinTree (Nav x l r _) = Node x l r

number_to_navtree : Int -> NavTree
number_to_navtree x = Nav x [] [] []

current_element : NavTree -> Maybe Int
current_element (NNil _) = Nothing
current_element (Nav x _ _ _) = Just x

current_path : NavTree -> (List PathNode)
current_path (NNil path) = path
current_path (Nav _ _ _ path) = path

move_to_left : NavTree -> NavTree
move_to_left (NNil path) = NNil path
move_to_left (Nav x l r path) = binTreeToNavTree l ((Right x r) :: path)

move_to_right : NavTree -> NavTree
move_to_right (NNil path) = NNil path
move_to_right (Nav x l r path) = binTreeToNavTree r ((Left x l) :: path)

at_leaf : NavTree -> Bool
at_leaf (NNil xs) = True
at_leaf _ = False

at_root : NavTree -> Bool
at_root (NNil []) = True
at_root (Nav _ _ _ []) = True
at_root _ = False

move_up2 : NavTree -> NavTree
move_up2 t = case (current_path t) of
                [] => t
                ((Left x l) :: path) => Nav x l (navTreeToBinTree t) path
                ((Right x r) :: path) => Nav x (navTreeToBinTree t) r path

sample_tree : NavTree
sample_tree = binTreeToNavTree (Node 13 (Node 12 [] []) (Node 14 [] [])) []