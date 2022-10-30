#lang eopl

(define (identifier? obj)
    (and (symbol? obj)
         (not (eqv? obj 'lambda))))

(define-datatype lc-exp lc-exp?
    (var-exp (var identifier?))
    (lambda-exp (bound-vars (list-of identifier?)) (body lc-exp?))
    (app-exp (rator lc-exp?) (rands (list-of lc-exp?))))

(define (parse-expression datum)
    (cond ((symbol? datum) (var-exp datum))
          ((pair? datum)
           (if (eqv? (car datum) 'lambda)
               (lambda-exp 
                    (cadr datum)
                    (parse-expression (caddr datum)))
               (app-exp
                    (parse-expression (car datum))
                    (map parse-expression (cdr datum)))))
          (else (report-invalid-concrete-syntax datum))))

(define (report-invalid-concrete-syntax datum)
    (eopl:error 'parse-expression "invalid syntax: ~s" datum))