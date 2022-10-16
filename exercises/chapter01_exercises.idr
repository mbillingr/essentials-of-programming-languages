
import Data.Vect


mutual
    data Sexpr = S String | L Slist

    Slist : Type
    Slist = List Sexpr


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
