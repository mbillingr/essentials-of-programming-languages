#lang eopl

; LETREC lang with ...
;  - continuation-passing interpreter

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))
      
(define the-grammar
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression
      ("-" "(" expression "," expression ")")
      diff-exp)
    
    (expression
      ("zero?" "(" expression ")")
      zero?-exp)

    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)

    (expression (identifier) var-exp)

    (expression
      ("let" identifier "=" expression "in" expression)
      let-exp)

    (expression
      ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" identifier ")" expression)
      proc-exp)

    (expression
      ("(" expression expression ")")
      call-exp)))


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
      (value-of/k exp1 (init-env) (end-cont)))))

(define (value-of/k exp env cont)
  (cases expression exp
    (const-exp (num) (apply-cont cont (num-val num)))
    (var-exp (var) (apply-cont cont (apply-env env var)))
    (proc-exp (var body)
      (apply-cont cont
        (proc-val (procedure var body env))))
    (letrec-exp (proc-name bound-var proc-body letrec-body)
      (value-of/k letrec-body 
                  (extend-env-rec proc-name bound-var proc-body env)
                  cont))
    (zero?-exp (exp1)
      (value-of/k exp1 env (zero1-cont cont)))
    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
    (let-exp (var exp1 body)
      (value-of/k exp1 env (let-exp-cont var body env cont)))
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont)))
    (call-exp (rator rand)
      (value-of/k rator env (rator-cont rand env cont)))))

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


(define (proc? val)
  (procedure? val))

(define (procedure var body env)
  (lambda (val cont)
    (value-of/k body (extend-env var val env) cont)))

(define (apply-procedure proc1 val cont)
  (proc1 val cont))


(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
  (extend-env-rec (p-name symbol?) (b-var symbol?) (body expression?) (env environment?)))

(define (apply-env env search-var)
  (cases environment env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env (var val parent) 
      (if (eqv? var search-var) 
        val 
        (apply-env parent search-var)))
    (extend-env-rec (p-name b-var p-body parent)
      (if (eqv? p-name search-var)
          (proc-val (procedure b-var p-body env))
          (apply-env parent search-var)))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))


(define (init-env)
  (extend-env 'i (num-val 1)
    (extend-env 'v (num-val 5)
      (extend-env 'x (num-val 10)
        (empty-env)))))


(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont 
    (cont continuation?))
  (let-exp-cont
    (var symbol?)
    (body expression?)
    (env environment?)
    (cont continuation?))
  (if-test-cont
    (exp2 expression?)
    (exp3 expression?)
    (env environment?)
    (cont continuation?))
  (diff1-cont 
    (exp2 expression?)
    (env environment?) 
    (cont continuation?))
  (diff2-cont 
    (val1 expval?)
    (cont continuation?))
  (rator-cont 
    (rand expression?)
    (env environment?)
    (cont continuation?))  
  (application-cont 
    (proc procedure?)
    (cont continuation?)))  

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
        (begin ;(println "End of computation.")
               val))
      (zero1-cont (saved-cont)
        (apply-cont saved-cont
          (bool-val (zero? (expval->num val)))))
      (let-exp-cont (var body saved-env saved-cont)
        (value-of/k body
          (extend-env var val saved-env) saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
        (value-of/k (if (expval->bool val) exp2 exp3)
                    saved-env saved-cont))
      (diff1-cont (exp2 env saved-cont)
        (value-of/k exp2 env (diff2-cont val saved-cont)))
      (diff2-cont (val1 saved-cont)
        (apply-cont saved-cont
          (num-val (- (expval->num val1) (expval->num val)))))
      (rator-cont (rand saved-env saved-cont)
        (value-of/k rand saved-env 
          (application-cont (expval->proc val) saved-cont)))
      (application-cont (proc saved-cont)
        (apply-procedure proc val saved-cont)))))

(define (println s)
  (display s)
  (newline))


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
  "letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in (double 6)"
  (num-val 12))

(newline)
(display "OK")
