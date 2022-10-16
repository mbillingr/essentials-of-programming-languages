
import Data.Vect


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
