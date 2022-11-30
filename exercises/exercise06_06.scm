#lang eopl

(define (value-of-simple-exp simple env)
    (cases simple-exp simple
        (const-exp (num)
          (num-val num))
        (var-exp (var)
          (apply-env env var))
        (cps-diff-exp (simple1 simple2)
          (num-val (- (expval->num (value-of-simple-exp simple1 env))
                      (expval->num (value-of-simple-exp simple2 env))))) 
        (cps-zero?-exp (simple1)
          (bool-val (zero? (expval->num (value-of-simple-exp simple1 env)))))
        (cps-proc-exp (vars body)
          (proc-val (procedure vars body env)))))
