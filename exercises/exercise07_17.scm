#lang eopl


(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
    (arg-type type?)
    (res-type type?))
  (tvar-type
    (sn number?)))


(define (apply-one-subst ty0 tvar ty1)
  (cases type ty0
    (int-type () (int-type))
    (bool-type () (bool-type))
    (proc-type (arg-type res-type)
      (proc-type
        (apply-one-subst arg-type tvar ty1)
        (apply-one-subst res-type tvar ty1)))
    (tvar-type (sn)
      (if (equal? ty0 tvar) ty1 ty0))))

(define (apply-subst-to-type ty subst)
  (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
        (proc-type
           (apply-subst-to-type t1 subst)
           (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
        (let ((tmp (assoc ty subst)))
          (if tmp 
              (apply-subst-to-type (cdr tmp) subst)
              ty)))))

(define (empty-subst) '())

(define (extend-subst subst tvar ty)
  (cons (cons tvar ty) subst))

(define (assert actual expected)  
  (if (equal? actual expected)
      (display ".")
      (eopl:error 'assert "~s != ~s" actual expected)))


; For this implementation, the no-occurrence invariant is definitely needed.
; Otherwise, apply-subst-to-type would recur infinitely.
; However, I'm starting to wonder, if the no-occurrence invariant is really needed for the book's
; original implementation. As far I can see, all the extend- and apply- functions are guaranteed to
; terminate. So the worst I'd expect to happen would be an unresolved (i.e. polymorphic) type 
; variable.


(define subst 
  (extend-subst
    (extend-subst 
      (empty-subst) 
      (tvar-type 0)
      (proc-type (tvar-type 1) (tvar-type 2)))
    (tvar-type 1)
    (proc-type (tvar-type 2) (tvar-type 3))))

(display (apply-subst-to-type (tvar-type 0) subst))
