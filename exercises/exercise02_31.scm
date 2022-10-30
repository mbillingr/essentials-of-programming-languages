#lang eopl


(define-datatype prefix-exp prefix-exp?
    (const-exp (num integer?))
    (diff-exp (op1 prefix-exp?) (op2 prefix-exp?)))


(define (parse-expression datum)
    (car (parse-expression-helper datum)))

(define (parse-expression-helper datum)
    (cond ((eqv? (car datum) '-)
           (let* ((pop1 (parse-expression-helper (cdr datum)))
                  (op1 (car pop1))
                  (rest1 (cdr pop1))
                  (pop2 (parse-expression-helper rest1))
                  (op2 (car pop2))
                  (rest-datum (cdr pop2)))
                 (cons (diff-exp op1 op2)
                       rest-datum))) 
          (else (cons (const-exp (car datum))
                      (cdr datum)))))

(display (parse-expression '(- - 3 2 - 4 - 12 7)))