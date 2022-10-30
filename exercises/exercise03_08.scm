#lang eopl

; LET lang with ...
;   - minus operator

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
      ("minus" "(" expression ")")
      minus-exp)
    (expression
      ("-" "(" expression "," expression ")")
      diff-exp)
    (expression
      ("+" "(" expression "," expression ")")
      add-exp)
    (expression
      ("*" "(" expression "," expression ")")
      mul-exp)
    (expression
      ("/" "(" expression "," expression ")")
      quot-exp)
    
    (expression
      ("zero?" "(" expression ")")
      zero?-exp)
    (expression
      ("equal?" "(" expression "," expression ")")
      equal?-exp)
    (expression
      ("less?" "(" expression "," expression ")")
      less?-exp)
    (expression
      ("greater?" "(" expression "," expression ")")
      greater?-exp)

    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)

    (expression (identifier) var-exp)

    (expression
      ("let" identifier "=" expression "in" expression)
      let-exp)))


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
      (value-of exp1 (init-env)))))

(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (var-exp (var) (apply-env env var))
    (minus-exp (exp1)
      (let* ((val1 (value-of exp1 env))
             (num1 (expval->num val1)))
        (num-val (- num1))))
    (diff-exp (exp1 exp2)
      (value-of-binop - exp1 exp2 env))
    (add-exp (exp1 exp2)
      (value-of-binop + exp1 exp2 env))
    (mul-exp (exp1 exp2)
      (value-of-binop * exp1 exp2 env))
    (quot-exp (exp1 exp2)
      (value-of-binop quotient exp1 exp2 env))
    (zero?-exp (exp1)
      (let* ((val1 (value-of exp1 env))
             (num1 (expval->num val1)))
        (if (zero? num1)
            (bool-val #t)
            (bool-val #f))))
    (equal?-exp (exp1 exp2)
      (value-of-comparison = exp1 exp2 env))
    (less?-exp (exp1 exp2)
      (value-of-comparison < exp1 exp2 env))
    (greater?-exp (exp1 exp2)
      (value-of-comparison > exp1 exp2 env))
    (if-exp (exp1 exp2 exp3)
      (let ((val1 (value-of exp1 env)))
        (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
    (let-exp (var exp1 body)
      (let ((val1 (value-of exp1 env)))
        (value-of body
          (extend-env var val1 env))))))

(define (value-of-binop op exp1 exp2 env)
  (let* ((val1 (value-of exp1 env))
         (val2 (value-of exp2 env))
         (num1 (expval->num val1))
         (num2 (expval->num val2)))
    (num-val (op num1 num2))))

(define (value-of-comparison op exp1 exp2 env)
  (let* ((val1 (value-of exp1 env))
         (val2 (value-of exp2 env))
         (num1 (expval->num val1))
         (num2 (expval->num val2)))
    (bool-val (op num1 num2))))


(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define (report-expval-extractor-error kind val)
  (eopl:error kind "expected ~s but got value ~s" kind val))


(define-datatype env-exp env-exp?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env env-exp?)))

(define (apply-env env search-var)
  (cases env-exp env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env (var val parent) 
      (if (eqv? var search-var) 
        val 
        (apply-env parent search-var)))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))


(define (init-env)
  (extend-env 'i (num-val 1)
    (extend-env 'v (num-val 5)
      (extend-env 'x (num-val 10)
        (empty-env)))))


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
  "minus (5)"
  (num-val -5))

(assert-eval
  "+ (9,4)"
  (num-val 13))

(assert-eval
  "* (9,4)"
  (num-val 36))

(assert-eval
  "/ (9,4)"
  (num-val 2))

(assert-eval
  "equal? (4,4)"
  (bool-val #t))

(assert-eval
  "less? (3,4)"
  (bool-val #t))

(assert-eval
  "greater? (4,3)"
  (bool-val #t))

(newline)
(display "OK")
