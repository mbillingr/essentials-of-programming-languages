


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