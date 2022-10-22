
import Data.List
import Data.Nat
import Data.Vect


mutual
    data Sexpr = S String | L Slist

    Slist : Type
    Slist = List Sexpr

Eq Sexpr where
    S a == S b = a == b
    L a == L b = a == b
    _ == _ = False


-- Exercise 1.15

||| Returns a list containing @n copies of @x.
duple : (n : Nat) -> (x : t) -> List t
duple 0 x = []
duple (S k) x = x :: duple k x



-- Exercise 1.16

||| Return the same list of 2-tuples but with each tuple's fields swapped.
invert : (List (a, b)) -> (List (b, a))
invert [] = []
invert ((x1, x2) :: xs) = (x2, x1) :: invert xs


-- Exercise 1.17

||| Wraps "parentheses" around each top-level element of lst
down : List t -> List (Vect 1 t)
down [] = []
down (x :: xs) = [x] :: down xs


-- Exercise 1.18

||| Returns the same slist, but with all occurences of s1 replaced by s2 and all occurrences of s2 replaced by s1.
swapper : String -> String -> Slist -> Slist
swapper s1 s2 [] = []
swapper s1 s2 ((L ys) :: xs) = (L (swapper s1 s2 ys)) :: swapper s1 s2 xs
swapper s1 s2 ((S x) :: xs) = 
    if x == s1 then 
        (S s2) :: swapper s1 s2 xs
    else if x == s2 then 
        (S s1) :: swapper s1 s2 xs
    else 
        (S x) :: swapper s1 s2 xs


-- Exercise 1.19

||| Returns a list like @lst, except that the @n-th element is @x.
list_set : (lst : List t) -> (n : Nat) -> (x : t) -> List t
list_set [] _ _ = []
list_set (_ :: xs) 0 x = x :: xs
list_set (y :: xs) (S k) x = y :: (list_set xs k x)


-- Exercise 1.20

mutual
    ||| Returns the number of occurences of @s in @slist.
    count_occurrences : (s : Sexpr) -> (slist : Slist) -> Nat
    count_occurrences s [] = 0
    count_occurrences s (x :: xs) = (count_sexpr_occurrences s x) + (count_occurrences s xs)

    ||| Returns the number of occurences of @s in @sexpr.
    count_sexpr_occurrences : (s : Sexpr) -> (sexpr : Sexpr) -> Nat
    count_sexpr_occurrences s sexpr = 
        if s == sexpr 
        then 1
        else case sexpr of
            (S x) => 0
            (L xs) => count_occurrences s xs


-- Exercise 1.21

||| Adds a prefix to each element of a list.
add_prefix : t -> List t -> List (Vect 2 t)
add_prefix x [] = []
add_prefix x (y :: ys) = [x, y] :: add_prefix x ys

||| Returns the cartesian product of two lists
product : List t -> List t -> List (Vect 2 t)
product [] _ = []
product _ [] = []
product (x :: xs) ys = (add_prefix x ys) ++ product xs ys


-- Exercise 1.22

||| Returns the list of elements in @lst that satisfy predicate @pred
filter_in : (pred : (t -> Bool)) -> (lst : List t) -> List t
filter_in pred [] = []
filter_in pred (x :: xs) = 
    let fxs = filter_in pred xs in
        if pred x then x :: fxs
                  else fxs


-- Exercise 1.23

||| Returns the 0-based position of the first element of @lst that satisfies the predicate @pred
list_index : (pred : (t -> Bool)) -> (lst : List t) -> Maybe Nat
list_index pred [] = Nothing
list_index pred (x :: xs) = 
    if pred x 
    then Just 0 
    else map (+ 1) (list_index pred xs)


-- Exercise 1.24

||| Returns False if any element of @lst fails to satisfies @pred, and returns True otherwise.
is_every : (pred : (t -> Bool)) -> (lst : List t) -> Bool
is_every pred [] = True
is_every pred (x :: xs) = (pred x) && (is_every pred xs)


-- Exercise 1.25

||| Returns True if any element of @lst satisfies @pred, and returns False otherwise.
does_exist : (pred : (t -> Bool)) -> (lst : List t) -> Bool
does_exist pred [] = False
does_exist pred (x :: xs) = (pred x) || (is_every pred xs)


-- Exercise 1.26

||| Remove a pair of parentheses from each top-level element of @lst
up : (lst : Slist) -> Slist
up [] = []
up ((L ys) :: xs) = ys ++ up xs
up (x :: xs) = x :: up xs


-- Exercise 1.27

||| Returns a list of the symbols contained in @slist in the order in which they would occur when printing @slist
flatten : Slist -> List String
flatten [] = []
flatten ((S x) :: xs) = x :: flatten xs
flatten ((L ys) :: xs) = flatten ys ++ flatten xs


-- Exercise 1.28
-- TODO: It would be nice if I'd also be able to prove that merging two sorted lists results in another sorted list...

||| Proof that one of the branches in merge indeed results in e Vect of correct length (the other branches don't need a proof)
mergeProof : Vect (S (S (plus len_1 len))) Int -> Vect (S (plus len_1 (S len))) Int
mergeProof (z::zs) = z :: (rewrite sym (plusSuccRightSucc len_1 len) in zs)

||| Merge two sorted lists to produce another sorted list
merge : (Vect n Int) -> (Vect m Int) -> (Vect (n + m) Int)
merge [] ys = ys
merge (x :: xs) [] = x :: Main.merge xs []
merge (x :: xs) (y :: ys) = 
    if y < x 
    then mergeProof (y :: Main.merge (x :: xs) ys)
    else x :: Main.merge xs (y :: ys)


-- Exercise 1.29

floor_half : Nat -> Nat
floor_half 0 = 0
floor_half (S 0) = 0
floor_half (S (S k)) = S (floor_half k)

ceil_half : Nat -> Nat
ceil_half 0 = 0
ceil_half (S 0) = 1
ceil_half (S (S k)) = S (ceil_half k)

||| Proof that ceil_half and floor_half add up to the original number
halvesAddUp : (n : Nat) -> n = ((ceil_half n) + (floor_half n))
halvesAddUp 0 = Refl
halvesAddUp (S 0) = Refl
halvesAddUp (S (S k)) = 
    rewrite sym (plusSuccRightSucc (ceil_half k) (floor_half k)) in 
    rewrite eqSucc k ((ceil_half k) + (floor_half k)) (halvesAddUp k) in 
        Refl

||| Returns two lists one containing every even-indexed element of the input list, the other every odd-indexed element
split : (Vect n t) -> ((Vect (ceil_half n) t), (Vect (floor_half n) t))
split [] = ([], [])
split (x :: []) = ([x], [])
split (x :: (y :: xs)) = let (a, b) = split xs in (x :: a, y :: b)

||| Returns a list of the elements in @loi in ascending order
sort : (Vect n Int) -> (Vect n Int)
sort [] = []
sort [x] = [x]
sort xs = 
    let (a, b) = split xs in 
        rewrite halvesAddUp n in (Main.merge (sort a) (sort b))


-- Exercise 1.30

||| Returns a list of elements sorted by the predicate
sort_predicate : (t -> t -> Bool) -> List t -> List t
sort_predicate pred [] = []
sort_predicate pred [x] = [x]
sort_predicate pred (pivot :: xs) = 
    (sort_predicate pred 
        (filter (not . (pred pivot)) xs)) 
    ++ [pivot] 
    ++ (sort_predicate pred 
        (filter (pred pivot) xs))


-- Exercise 1.31

data BinTree = Leaf Int
             | Node String BinTree BinTree

is_leaf : BinTree -> Bool
is_leaf (Leaf _) = True
is_leaf (Node _ _ _) = False


-- Exercise 1.32

double_tree : BinTree -> BinTree
double_tree (Leaf x) = Leaf (x + x)
double_tree (Node s l r) = Node s (double_tree l) (double_tree r)


-- Exercise 1.33

mark_leaves_with_red_depth : BinTree -> BinTree
mark_leaves_with_red_depth = mark 0 where
    mark : Int -> BinTree -> BinTree
    mark d (Leaf _) = Leaf d
    mark d (Node "red" l r) = Node "red" (mark 0 l) (mark 0 r)
    mark d (Node s l r) = Node s (mark (d+1) l) (mark (d+1) r)


-- Exercise 1.34
-- It would be interesting to see if it is possible to enforce correctness of the BST using types/proofs

data BinSearchTree = Empty | Entry Int BinSearchTree BinSearchTree

data Direction = Left | Right

path : Int -> BinSearchTree -> List Direction
path _ Empty = []
path k (Entry x l r) = 
    if k == x
    then []
    else if k < x
         then Left :: path k l
         else Right :: path k r


-- Exercise 1.35

number_leaves : BinTree -> BinTree
number_leaves tree = fst (numl tree 0) where
    numl : BinTree -> Int -> (BinTree, Int)
    numl (Leaf _) n = ((Leaf n), n + 1)
    numl (Node s l r) n = 
        let (tl, nl) = numl l n in
        let (tr, nr) = numl r nl in ((Node s tl tr), nr)
