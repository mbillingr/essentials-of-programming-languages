Exercise 1.1
============

1. `S = {3n + 2 | n ∈ N}`
   - Top-down:
     A natural number n is in S iff either
     1. n = 2
     2. n-3 ∈ S
   - Bottom-up:
     S is the smallest set contained in N that satisfies
     1. 2 ∈ S
     2. if n ∈ S, then n+3 ∈ S
   - Inference Rules:
     ```
     -------
      2 ∈ S
     
       n ∈ S
     ---------
      n+3 ∈ S
     ```
     
2. `S = {2n + 3m + 1 | n,m ∈ N}` 
   - Top-down:
     A natural number k is in S iff any
     1. k = 1
     2. k-2 ∈ S
     3. k-3 ∈ S
   - Bottom-up:
     S is the smallest set contained in N that satisfies
     1. 1 ∈ S
     2. if n ∈ S, then n+2 ∈ S
     3. if n ∈ S, then n+3 ∈ S
   - Inference Rules:
     ```
     -------
      1 ∈ S
     
       n ∈ S
     ---------
      n+2 ∈ S
     
       n ∈ S
     ---------
      n+3 ∈ S
     ```
     
3. `S = {(n, 2n + 1) | n ∈ N}` 
   - Top-down
     A pair (a, d) of two natural numbers is in S iff either
     1. (a, d) = (0, 1)
     2. (a-1, d-2) ∈ S
   - Bottom-up
     S is the smallest set contained in N that satisfies
     1. (0, 1) ∈ S
     2. if (a, d) ∈ S, then (a+1, d+2) ∈ S
   - Inference Rules:
     ```
     ------------
      (0, 1) ∈ S
     
        (a, d) ∈ S
     ----------------
      (a+1, d+2) ∈ S
     ```
     
4. `S = {(n, n^2) | n ∈ N}` 
   - Top-down
     A pair (a, d) of two natural numbers is in S iff either
     1. (a, d) = (0, 0)
     2. (a-1, d - 2a + 1) ∈ S
   - Bottom-up
     S is the smallest set contained in N that satisfies
     1. (0, 0) ∈ S
     2. if (a, d) ∈ S, then (a+1, d+2a+1) ∈ S
   - Inference Rules:
     ```
     ------------
      (0, 0) ∈ S
     
            (a, d) ∈ S
     -----------------------
      (a+1, d + 2a + 1) ∈ S
     ```
     
Exercise 1.2
============
1. `S = {(n, n*7+1) | n ∈ N`
2. `S = {(n, 2^n) | n ∈ N`
3. `S = {(n, fib(n-1), fib(1)) | n ∈ N`
4. `S = {(n, 2n+1, n^2) | n ∈ N`
