#lang eopl

(define (number->bintree n)
    (list n '() '()))

(define (at-leaf? tree)
    (null? tree))

(define (current-element tree)
    (car tree))

(define (move-to-left-son tree)
    (cadr tree))

(define (move-to-right-son tree)
    (caddr tree))

(define (insert-to-left item tree)
    (list (current-element tree)
          (list item (cadr tree) '())
          (caddr tree)))

(define (insert-to-right item tree)
    (list (current-element tree)
          (cadr tree)
          (list item '() (caddr tree))))