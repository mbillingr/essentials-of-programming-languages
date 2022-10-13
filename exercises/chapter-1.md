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
1. `S = {(n, n*7+1) | n ∈ N}`
2. `S = {(n, 2^n) | n ∈ N}`
3. `S = {(n, fib(n-1), fib(1)) | n ∈ N}`
4. `S = {(n, 2n+1, n^2) | n ∈ N}`

Exercise 1.3
============
T is not constrained to be the smallest set satisfying 0 ∈ T and (n ∈ T) -> (n+3 ∈ T). Otherwise, the definition is similar to S. 
Thus, any superset of S of the form `T = S ∪ {n*3+X | n ∈ N}` would work. Even the whole set of natural numbers `T = N` satisfies the condition.

Exercise 1.4
============
```
   List-of-Int
=> (Int . List-of-Int)
=> (-7 . List-of-Int)
=> (-7 . (Int . List-of-Int))
=> (-7 . (3 . List-of-Int))
=> (-7 . (3 . (Int . List-of-Int)))
=> (-7 . (3 . (14 . List-of-Int)))
=> (-7 . (3 . (14 . ())))
```

Exercise 1.5
============
1. IH is true for identifiers, because they contain no parentheses.
2. IH is true for lambda expressions if it is true for the subexpression, because the lambda adds two opening and two closing parenthesis.
3. IH is true for calls if it is true for both subexpressions, because the call adds one opening and one closing parenthesis.

Exercise 1.6
============
I assume that order of tests refers to the conditions of the two ifs.
If we simply swapped the conditions, the function behavior would be totally wrong. Instead, we would have to shuffle the branches a bit:
```scheme
(if (zero? n)
    (car lst)
    (if (null? lst)
        (report-list-too-short n)
        (nth-element (cdr lst) (- n 1))))
```
This is more correct, but could cause `car` being called on an empty list. We'd have to duplicate the `null?` check in both branches of the outer if.

Exercise 1.7
============
Solution that does not rely on non-local control flow such as exceptions. Would have been nicer to put the original arguments in the closure of a local recursion helper, but I'm not sure yet if local definitions are allowed, since the book uses define with lambda so far.
```scheme
(define nth-element
  (lambda (lst n)
    (nth-element-recursion-helper lst n lst)))
        
(define nth-element-recursion-helper
  (lambda (lst n original n0)
    (if (null? lst)
      (report-list-too-short n original n0)
      (if (zero? n)
        (car lst)
        (nth-element (cdr lst) (- n 1) original n0)))))

(define report-list-too-short
  (lambda (n lst)
    (error 'nth-element
      "List ~s does not have ~s elements.~%" lst n)))
```

Exercise 1.8
============
This time in Idris:
```idris
remove_until : String -> (List String) -> (List String)
-- usage: (remove_until s los) returns the tail of los
--        after the first occurence of s.
remove_until s [] = []
remove_until s (x :: xs) = 
    if x == s
        then xs
        else remove_until s xs
```