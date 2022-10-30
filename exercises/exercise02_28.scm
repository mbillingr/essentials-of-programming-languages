#lang eopl

(define (identifier? obj)
    (and (symbol? obj)
         (not (eqv? obj 'lambda))))

(define-datatype lc-exp lc-exp?
    (var-exp (var identifier?))
    (lambda-exp (bound-var identifier?) (body lc-exp?))
    (app-exp (rator lc-exp?) (rand lc-exp?)))

(define (unparse-lc-exp exp)
    (cases lc-exp exp
        (var-exp (var) 
            (symbol->string var))
        (lambda-exp (bound-var body)
            (string-append "proc "
                           (symbol->string bound-var)
                           " => "
                           (unparse-lc-exp body)))
        (app-exp (rator rand)
            (string-append (unparse-lc-exp rator)
                           "("
                           (unparse-lc-exp rand)
                           ")"))))

; Actually, the exercise asked to implement the unparser for the SECOND grammar, 
; which is the scheme-syntax version of the grammar. Taking the scheme value 
; returned by unparse-lc-exp from page 53 and converting it to string would
; solve the exercise trivially.
; I implemented the FIRST grammar instead, which seems more interesting.
; Also, I think that grammar is ambiguous. The resulting example could be equivalent
; to any of the following expressions:
;  1. (((lambda (a) a) b) c)
;  2. ((lambda (a) (a b)) c)
;  3. (lambda (a) ((a b) c))

(display
    (unparse-lc-exp 
        (app-exp 
            (lambda-exp 'a 
                (app-exp (var-exp 'a) (var-exp 'b))) 
            (var-exp 'c))))