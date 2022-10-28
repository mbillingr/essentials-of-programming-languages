


-- Exercise 2.1
-- See exercise02_01.py and .png files

-- Exercise 2.2
{- 
The data type specifies numbers of up to infinite size. None of the implementations can realistically achieve this.

The Unary representation will fail to compute a successor if it runs out of heap memory. This may happen early, because every increment is an allocation.
It will also cause an error for (predecessor (zero)), which is acceptable under the specification.

The Scheme number representation can produce negative numbers, which is acceptable under the specification.
Depending on the implementation of Scheme values, the successor/predecessor operations may fail for numbers exceeding a certain magnitude.

Similar to the Unary implementation, the Bigit implementation is limited by the available heap. However, it will reach this limit later than the Unary 
implementation because it uses allocations more efficiently (by a factor of N).
-}


-- Exercise 2.3

data DiffTree = One | Diff DiffTree DiffTree

reify :  DiffTree -> Int
reify One = 1
reify (Diff x y) = (reify x) - (reify y)

-- 1. Show that every number has infinitely many representations in this system:
--    Since (Diff n (Diff One One)) is the same as n - 0, the number n can be extended infinitely often without changing it. And this is only one of the infinitely many possible transformations.

-- 2

zero : DiffTree
zero = Diff One One

equals : DiffTree -> DiffTree -> Bool
equals x y = (reify x) == (reify y)  -- this feels like cheating... maybe it should be done without conversion to integers?

is_zero : DiffTree -> Bool
is_zero One = False
is_zero (Diff x y) = equals x y

negation : DiffTree -> DiffTree
negation One = Diff zero One
negation (Diff x y) = Diff y x

successor : DiffTree -> DiffTree
successor One = Diff One (negation One)
successor (Diff x y) = Diff (successor x) y

predecessor : DiffTree -> DiffTree
predecessor One = zero
predecessor (Diff x y) = Diff x (successor y)

-- 3

diff_tree_plus : DiffTree -> DiffTree -> DiffTree
diff_tree_plus x y = Diff x (negation y)
