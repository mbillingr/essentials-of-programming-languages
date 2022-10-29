#lang eopl

(define (any? obj) #t)

(define-datatype Stack Stack?
    (empty-stack)
    (push-stack (stack Stack?) (value any?)))

(define (top-stack stack)
    (cases Stack stack
        (empty-stack () 
            (report-empty-stack 'top-stack))
        (push-stack (substack value) 
            value)))

(define (pop-stack stack)
    (cases Stack stack
        (empty-stack () 
            (report-empty-stack 'top-stack))
        (push-stack (substack value) 
            substack)))

(define (report-empty-stack func)
    (eopl:error func "empty stack"))