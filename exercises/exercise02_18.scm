#lang eopl

(define (number->sequence n)
    (list n '() '()))

(define (current-element seq)
    (car seq))

(define (at-left-end? seq)
    (null? (cadr seq)))

(define (at-right-end? seq)
    (null? (caddr seq)))

(define (move-to-left seq)
    (list (caadr seq)
          (cdadr seq)
          (cons (car seq) (caddr seq))))

(define (move-to-right seq)
    (list (caaddr seq)
          (cons (car seq) (cadr seq))
          (cdaddr seq)))

(define (insert-to-left item seq)
    (list (car seq)
          (cons item (cadr seq))
          (caddr seq)))

(define (insert-to-right item seq)
    (list (car seq)
          (cadr seq)
          (cons item (caddr seq))))