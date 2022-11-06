#lang eopl

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
      ("letrec" identifier "(" (arbno identifier) ")" "=" expression "in" expression)
      letrec-exp)

    (expression
      ("(" expression (arbno expression) ")")
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
      (value-of exp1 (init-env)))))

(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (var-exp (var) (apply-env env var))
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
    (let-exp (var exp1 body)
      (let ((val1 (value-of exp1 env)))
        (value-of body
          (extend-env var val1 env))))
    (letrec-exp (proc-name bound-var* proc-body letrec-body)
      (value-of letrec-body 
                (extend-env-rec proc-name bound-var* proc-body env)))
    (call-exp (rator rand*)
      (let ((proc (expval->proc (value-of rator env)))
            (arg* (map (lambda (r) (value-of r env)) rand*)))
        (apply-procedure proc arg*)))))

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

(define (procedure var* body env)
  (lambda (val*)
    (value-of body (extend-env* var* val* env))))

(define (apply-procedure proc1 val*)
  (proc1 val*))


(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
  (extend-env-rec (p-name symbol?) (b-var* (list-of symbol?)) (body expression?) (env environment?)))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr vals)
        (extend-env (car vars) (car vals) env))))

(define (apply-env env search-var)
  (cases environment env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env (var val parent) 
      (if (eqv? var search-var) 
        val 
        (apply-env parent search-var)))
    (extend-env-rec (p-name b-var* p-body parent)
      (if (eqv? p-name search-var)
          (proc-val (procedure b-var* p-body env))
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
  "letrec times(x y) = if zero?(x) then 0 else -((times -(x,1) y), -(0,y))
   in (times 6 3)"
  (num-val 18))

(newline)
(display "OK")
