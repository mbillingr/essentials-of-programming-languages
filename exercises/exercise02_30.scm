#lang eopl

(define (identifier? obj)
    (and (symbol? obj)
         (not (eqv? obj 'lambda))))

(define-datatype lc-exp lc-exp?
    (var-exp (var identifier?))
    (lambda-exp (bound-var identifier?) (body lc-exp?))
    (app-exp (rator lc-exp?) (rand lc-exp?)))

(define (parse-expression datum)
    (cond ((symbol? datum) (var-exp datum))
          ((pair? datum)
           (if (eqv? (car datum) 'lambda)
               (parse-lambda datum)
               (parse-app datum)))
          (else (report-invalid-concrete-syntax datum))))

(define (parse-lambda datum)
    (cond ((null? (cdr datum))
           (report-missing-parameter-list-and-function-body datum))
          ((not (pair? (cadr datum)))
           (report-invalid-parameter-list datum))
          ((not (null? (cdadr datum)))
           (report-invalid-parameter-list datum))
          ((null? (cddr datum))
           (report-invalid-function-body datum))
          ((not (null? (cdddr datum))) 
           (report-invalid-function-body datum))
          (else
            (lambda-exp 
                (caadr datum)
                (parse-expression (caddr datum))))))

(define (parse-app datum)
    (if (and (pair? (cdr datum))
             (null? (cddr datum)))
        (app-exp
            (parse-expression (car datum))
            (parse-expression (cadr datum)))
        (report-wrong-number-of-arguments datum)))

(define (report-invalid-concrete-syntax datum)
    (eopl:error 'parse-expression "invalid syntax: ~s" datum))

(define (report-missing-parameter-list-and-function-body datum)
    (eopl:error 'parse-lambda "no parameter list and function body in ~s" datum))

(define (report-invalid-parameter-list datum)
    (eopl:error 'parse-lambda "expected list with exactly one function parameter in ~s" datum))

(define (report-invalid-function-body datum)
    (eopl:error 'parse-lambda "invalid function body in in ~s" datum))

(define (report-wrong-number-of-arguments datum)
    (eopl:error 'parse-app "expected exactly one function argument in ~s" datum))