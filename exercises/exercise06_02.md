
Hypothesis:
    (fib/k n g) = (g (fib n))

Base Cases:
    (fib 0 g) = (g 1) = (g (fib 0))
    (fib 1 g) = (g 1) = (g (fib 1))

Induction:
    (fib/k n+1 g)
    = (fib/k n (lambda (v1) (fib/k n-1 (lambda (v2) (g (+ v1 v2))))))
    = ((fib/k n-1 (lambda (v2) (g (+ v1 v2)))) (fib n))  ; by the hypothesis
    = (fib/k n-1 (lambda (v2) (g (+ (fib n) v2))))
    = ((lambda (v2) (g (+ (fib n) v2))) (fib n-1))  ; by the hypothesis
    = (g (+ (fib n) (fib n-1)))
    = (g (fib n+1))
