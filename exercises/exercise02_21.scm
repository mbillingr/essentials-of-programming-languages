#lang eopl

(define (any? obj) #t)

(define-datatype Env-exp Env-exp?
    (empty-env)
    (extend-env (identifier symbol?) (value any?) (env Env-exp?)))

(define (apply-env env search-var)
    (cases Env-exp env
        (empty-env () 
            (report-no-binding-found search-var))
        (extend-env (var val parent) 
            (if (eqv? var search-var) 
                val 
                (apply-env parent search-var)))))

(define (has-binding? env search-var)
    (cases Env-exp env
        (empty-env () #f)
        (extend-env (var val parent) 
            (if (eqv? var search-var) 
                #t 
                (apply-env parent search-var)))))

(define (report-no-binding-found var)
    (eopl:error 'apply-env "No binding for ~s" var))