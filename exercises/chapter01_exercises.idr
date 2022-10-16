

-- Exercise 1.15


||| Returns a list containing @n copies of @x
duple : Nat -> t -> List t
duple 0 x = []
duple (S k) x = x :: duple k x