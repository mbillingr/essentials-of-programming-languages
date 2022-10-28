


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


-- Exercise 2.4
{-
(empty-stack)      = [0]
(push [f] v)       = [g], where (top [g]) = v
(pop [f])          = [g], so that (pop (push [g] _)) = g
(top [f])          = v if [f] = (push _ v), #f otherwise
(empty-stack? [f]) = #t if [f] == [0], #f otherwise
 -}


-- Exercise 2.5

data Env a = Empty | Entry String a (Env a)

empty_env : Env a
empty_env = Empty

extend_env : String -> a -> (Env a) -> (Env a)
extend_env = Entry

apply_env : (Env a) -> String -> (Maybe a)
apply_env Empty searchvar = Nothing
apply_env (Entry var val e) searchvar =
    if var == searchvar
    then Just val
    else apply_env e searchvar

-- Exercise 2.6

Env1 : Type -> Type
Env1 a = String -> Maybe a

empty_env1 : Env1 a
empty_env1 var = Nothing

extend_env1 : String -> a -> (Env1 a) -> (Env1 a)
extend_env1 var val env = lookup where
    lookup : Env1 a
    lookup searchvar = if var == searchvar
                       then Just val
                       else env searchvar

apply_env1 : Env1 a -> String -> Maybe a
apply_env1 env = env

-- Representing the environment with functions is pretty much the most interesting implementation I can come up with.
-- Other solutions would be variants of  the a-list implementation, or maybe using a mutable key/value store such as a hashmap... I'll spare myself the effort.

-- Exercise 2.7
-- I'm not sure what a more informative error maessage would contain. 
-- Maybe the original env in that we started the search? In that case, I would capture the env passed to (apply-env) in 
-- the closure of an inner recursion helper function. Then it would be available when producing the error message.
-- It does not seem worth to actually implement that.


-- Exercise 2.8

is_empty : Env a -> Bool
is_empty Empty = True
is_empty _ = False


-- Exercise 2.9

has_binding : Env a -> String -> Bool
has_binding Empty _ = False
has_binding (Entry var _ env) searchvar = 
    if var == searchvar
    then True
    else has_binding env searchvar
