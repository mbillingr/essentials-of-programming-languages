#lang eopl

; NAMELESS lang with ...
;   - function inlining

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
      ("proc" "(" identifier ")" expression)
      proc-exp)

    (expression
      ("(" expression expression ")")
      call-exp)

    (expression ("%lexref" number) nameless-var-exp)

    (expression
      ("%let" expression "in" expression)
      nameless-let-exp)

    (expression
      ("%lexproc" expression)
      nameless-proc-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (let* ((ast1 (scan&parse source))
         (ast2 (translation-of-program ast1)))
    (value-of-program ast2)))

(define (translation-of-program pgm)
  (cases program pgm
    (a-program (exp1)
      (a-program
        (translation-of exp1 (empty-senv))))))

(define (translation-of exp senv)
  (cases expression exp
    (const-exp (num) (const-exp num))
    (diff-exp (exp1 exp2)
      (diff-exp (translation-of exp1 senv)
                (translation-of exp2 senv)))
    (zero?-exp (exp1)
      (zero?-exp (translation-of exp1 senv)))
    (if-exp (exp1 exp2 exp3)
      (if-exp (translation-of exp1 senv)
              (translation-of exp2 senv)
              (translation-of exp3 senv)))
    (var-exp (var)
      (nameless-var-exp
        (apply-senv senv var)))
    (let-exp (var exp1 body)
      (let* ((letval (translation-of exp1 senv))
             (new-env (cases expression letval
                        (nameless-proc-exp (f-body)
                          (extend-senv-proc var f-body senv))
                        (else (extend-senv var senv)))))
        (nameless-let-exp
          letval
          (translation-of body new-env))))
    (proc-exp (var body)
      (nameless-proc-exp
        (translation-of body
          (extend-senv var senv))))
    (call-exp (rator rand)
      (cases expression rator
        (var-exp (var) 
          (if (known-function? senv var)
              (translation-of-known-function-application var rand senv)
              (call-exp (translation-of rator senv)
                    (translation-of rand senv))))
        (else
          (call-exp (translation-of rator senv)
                    (translation-of rand senv)))))
    (else
      (report-invalid-source-expression exp))))

(define (report-invalid-source-expression exp)
  (eopl:error 'translation-of "Invalid source expression ~s" exp))

(define (translation-of-known-function-application var rand senv)
  (let* ((f-offset (apply-senv senv var))
         (body (lookup-body senv var)))
    (nameless-let-exp
      (translation-of rand senv)
      body)))


(define-datatype senv senv?
  (empty-senv)
  (variable (var symbol?) (env senv?))
  (function (var symbol?) (body expression?) (env senv?)))

(define (extend-senv var senv)
  (variable var senv))

(define (extend-senv-proc var body senv)
  (function var body senv))

(define (known-function? env search-var)
  (cases senv env
    (empty-senv () #f)
    (variable (var next-env)
      (if (eqv? var search-var)
          #f
          (known-function? next-env search-var)))
    (function (var body next-env)
      (if (eqv? var search-var)
          #t
          (known-function? next-env search-var)))))

(define (lookup-body env search-var)
  (define (iterate env offset)
    (cases senv env
      (empty-senv ()
        (report-unbound-var search-var))
      (variable (var next-env)
        (if (eqv? var search-var)
            (report-unbound-var search-var)
            (iterate next-env (+ 1 offset))))
      (function (var body next-env)
        (if (eqv? var search-var)
            (shift-references body offset 1)
            (iterate next-env (+ 1 offset))))))
  (iterate env 1))

(define (apply-senv env search-var)
  (cases senv env
    (empty-senv ()
      (report-unbound-var search-var))
    (variable (var next-env)
      (if (eqv? var search-var)
          0
          (+ 1 (apply-senv next-env search-var))))
    (function (var body next-env)
      (if (eqv? var search-var)
          0
          (+ 1 (apply-senv next-env search-var))))))

(define (report-unbound-var var)
  (eopl:error 'apply-senv "Unbound variable ~s" var))


(define (shift-references exp offset minimum)
  (cases expression exp
    (const-exp (num) (const-exp num))
    (diff-exp (exp1 exp2)
      (diff-exp (shift-references exp1 offset minimum)
                (shift-references exp2 offset minimum)))
    (zero?-exp (exp1)
      (zero?-exp (shift-references exp1 offset minimum)))
    (if-exp (exp1 exp2 exp3)
      (if-exp (shift-references exp1 offset minimum)
              (shift-references exp2 offset minimum)
              (shift-references exp3 offset minimum)))
    (call-exp (rator rand)
      (call-exp (shift-references rator offset minimum)
                (shift-references rand offset minimum)))
    (nameless-var-exp (n) 
      (if (>= n minimum)
          (nameless-var-exp (+ n offset))
          (nameless-var-exp n)))
    (nameless-let-exp (exp1 body)
      (nameless-let-exp
        (shift-references exp1 offset minimum)
        (shift-references body offset (+ 1 minimum))))
    (nameless-proc-exp (body)
      (nameless-proc-exp
        (shift-references body offset (+ 1 minimum))))
    (else
      (report-invalid-translated-expression exp))))


(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
      (value-of exp1 (empty-nameless-env)))))

(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (diff-exp (exp1 exp2)
      (let* ((val1 (value-of exp1 env))
             (val2 (value-of exp2 env))
             (num1 (expval->num val1))
             (num2 (expval->num val2)))
        (num-val (- num1 num2))))
    (zero?-exp (exp1)
      (let* ((val1 (value-of exp1 env))
             (num1 (expval->num val1)))
        (if (zero? num1)
            (bool-val #t)
            (bool-val #f))))
    (if-exp (exp1 exp2 exp3)
      (let ((val1 (value-of exp1 env)))
        (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
    (call-exp (rator rand)
      (let ((proc (expval->proc (value-of rator env)))
            (arg (value-of rand env)))
        (apply-procedure proc arg)))
    (nameless-var-exp (n) (apply-nameless-env env n))
    (nameless-let-exp (exp1 body)
      (let ((val (value-of exp1 env)))
        (value-of body
          (extend-nameless-env val env))))
    (nameless-proc-exp (body)
      (proc-val (procedure body env)))
    (else
      (report-invalid-translated-expression exp))))

(define (report-invalid-translated-expression exp)
  (eopl:error 'value-of "Invalid translated expression ~s" exp))


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
    (body expression?)
    (saved-nameless-env nameless-environment?)))

(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (body env)
      (value-of body (extend-nameless-env val env)))))


(define (nameless-environment? x)
  ((list-of expval?) x))

(define (empty-nameless-env) '())
(define extend-nameless-env cons)
(define apply-nameless-env list-ref)


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
  "let x = 3 in let f = proc (y) -(y,x) in (f 13)"
  ;%let 3 in let proc -(#0,#1) in (#0 13)
  ;%let 3 in let proc -(#0,#1) in let 13 in -(#0,#2)
  (num-val 10))

(assert-eval
  "let x = 3 in let f = proc (y) let z = 0 in -(y,x) in (f 13)"
  ; let 3 in let proc let 0 in -(#1,#2) in (#0 13)
  ; let 3 in let proc let 0 in -(#1,#2) in let 13 in let 0 in -(#1,#3)
  (num-val 10))

(assert-eval
  "let x = 3 in let f = proc (y) -(y,x) in let z = 0 in (f 13)"
  (num-val 10))

(newline)
(display "OK")
