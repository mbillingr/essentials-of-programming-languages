#lang eopl

(define (identifier? obj)
    (and (symbol? obj)
         (not (eqv? obj 'lambda))))

(define-datatype lc-exp lc-exp?
    (var-exp (var identifier?))
    (lambda-exp (bound-var identifier?) (body lc-exp?))
    (app-exp (rator lc-exp?) (rand lc-exp?)))

(define (report-empty-stack func)
    (eopl:error func "empty stack"))