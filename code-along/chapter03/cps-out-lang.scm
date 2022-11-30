#lang eopl

; CPS-OUT lang (interpreter)

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))
      
(define the-grammar
  '((program (tfexp) a-program)

    (simple-exp 
      (number) 
      const-exp)

    (simple-exp
      (identifier) 
      var-exp)

    (simple-exp
      ("-" "(" simple-exp "," simple-exp ")")
      cps-diff-exp)

    (simple-exp
      ("+" "(" (separated-list simple-exp ",") ")")
      cps-sum-exp)
    
    (simple-exp
      ("zero?" "(" simple-exp ")")
      cps-zero?-exp)

    (simple-exp
      ("proc" "(" (arbno identifier) ")" tfexp)
      cps-proc-exp)

    (tfexp
      (simple-exp)
      simple-exp->exp)

    (tfexp
      ("let" identifier "=" simple-exp "in" tfexp)
      cps-let-exp)

    (tfexp
      ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp) "in" tfexp)
      cps-letrec-exp)

    (tfexp
      ("if" simple-exp "then" tfexp "else" tfexp)
      cps-if-exp)

    (tfexp
      ("(" simple-exp (arbno simple-exp) ")")
      cps-call-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (value-of-program (scan&parse source)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
      (value-of/k exp1 (empty-env) (end-cont)))))

(define (value-of/k exp env cont)
  (cases tfexp exp
    (simple-exp->exp (simple) 
      (apply-cont cont
        (value-of-simple-exp simple env)))
    (cps-let-exp (var rhs body)
      (let ((val (value-of-simple-exp rhs env)))
        (value-of/k body
          (extend-env* (list var) (list val) env)
          cont)))
    (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
      (value-of/k letrec-body 
        (extend-env-rec** p-names b-varss p-bodies env)
        cont))
    (cps-if-exp (simple1 body1 body2)
      (if (expval->bool (value-of-simple-exp simple1 env))
          (value-of/k body1 env cont)
          (value-of/k body2 env cont)))
    (cps-call-exp (rator rands)
      (let ((rator-proc (expval->proc (value-of-simple-exp rator env)))
            (rand-vals (map (lambda (simple) (value-of-simple-exp simple env)) rands)))
        (apply-procedure/k rator-proc rand-vals cont)))))

(define (value-of-simple-exp simple env)
  (cases simple-exp simple
    (const-exp (num)
      (num-val num))
    (var-exp (var)
      (apply-env env var))
    (cps-diff-exp (simple1 simple2)
      (num-val (- (expval->num (value-of-simple-exp simple1 env))
                  (expval->num (value-of-simple-exp simple2 env))))) 
    (cps-sum-exp (simples)
      (num-val (apply + (map (lambda (x) (expval->num (value-of-simple-exp x env))) simples))))
    (cps-zero?-exp (simple1)
      (bool-val (zero? (expval->num (value-of-simple-exp simple1 env)))))
    (cps-proc-exp (vars body)
      (proc-val (procedure vars body env)))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define (expval->proc val)    
  (cases expval val
    (proc-val (proc) proc)
    (else (report-expval-extractor-error 'proc val))))

(define (report-expval-extractor-error kind val)
  (eopl:error kind "expected ~s but got value ~s" kind val))


(define-datatype proc proc?
  (procedure
    (vars (list-of symbol?))
    (body tfexp?)
    (env environment?)))    

(define (apply-procedure/k proc1 args cont)
  (cases proc proc1
    (procedure (vars body saved-env)
      (value-of/k body
        (extend-env* vars args saved-env)
        cont))))


(define-datatype environment environment?
  (empty-env)
  (extend-env* 
    (var (list-of symbol?)) 
    (val (list-of expval?)) 
    (env environment?))
  (extend-env-rec** 
    (p-names (list-of symbol?)) 
    (b-varss (list-of (list-of symbol?))) 
    (p-bodies (list-of tfexp?)) 
    (env environment?)))

(define (apply-env env search-var)
  (cases environment env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env* (vars vals saved-env) 
      (lookup search-var vars vals saved-env))
    (extend-env-rec** (p-names b-varss p-bodies saved-env)
      (lookup-rec search-var p-names b-varss p-bodies env saved-env))))

(define (lookup search-var vars vals next-env)
  (cond ((null? vars)
         (apply-env next-env search-var))
        ((eqv? (car vars) search-var)
         (car vals))
        (else
          (lookup search-var (cdr vars) (cdr vals) next-env))))

(define (lookup-rec search-var p-names b-varss p-bodies current-env next-env)
  (cond ((null? p-names)
         (apply-env next-env search-var))
        ((eqv? (car p-names) search-var)
         (proc-val
           (procedure
             (car b-varss)
             (car p-bodies)
             current-env)))
        (else
          (lookup-rec search-var (cdr p-names) (cdr b-varss) (cdr p-bodies) current-env next-env))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))


(define-datatype continuation continuation?
  (end-cont))

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
        (begin ;(println "End of computation.")
               val)))))

(define (assert-eval src expected-val)
  (let ((val (run src)))
    (if (equal? val expected-val)
        (display ".")
        (eopl:error 'assert-eq "~s evaluates to ~s but expected ~s" src val expected-val))))


(assert-eval 
  "42" 
  (num-val 42))

(assert-eval
  "-(8,5)"
  (num-val 3))

(assert-eval
  "zero? (0)"
  (bool-val #t))

(assert-eval
  "zero? (5)"
  (bool-val #f))

(assert-eval
  "if zero? (0) then 1 else 2"
  (num-val 1))

(assert-eval
  "if zero? (9) then 1 else 2"
  (num-val 2))

(assert-eval
  "let x = 123 in x"
  (num-val 123))

(assert-eval
  "let x = 123 in (proc (x) x 42)"
  (num-val 42))

(assert-eval
  "letrec 
     finish(x) = x
     double(x k) = 
       if zero?(x) 
       then (k x) 
       else letrec double1(y) = (k +(y, 2))
            in (double -(x,1) double1)
   in (double 6 finish)"
  (num-val 12))

(newline)
(display "OK")
