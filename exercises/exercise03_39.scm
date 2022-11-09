#lang eopl

; NAMELESS lang with ...
;   - cond
;   - list construction operator
;   - list unpacking

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
    (expression
      ("cond" (arbno expression "==>" expression) "end")
      cond-exp)

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

    (expression
      ("list" "(" (separated-list expression ",") ")")
      list-exp) 
    (expression
      ("unpack" (arbno identifier) "=" expression "in" expression)
      unpack-exp)

    (expression ("%lexref" number) nameless-var-exp)

    (expression
      ("%let" expression "in" expression)
      nameless-let-exp)

    (expression
      ("%lexproc" expression)
      nameless-proc-exp)

    (expression
      ("%unpack" number expression "in" expression)
      nameless-unpack-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (value-of-program 
    (translation-of-program
      (scan&parse source))))

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
    (cond-exp (exp1* exp2*)
      (cond-exp
        (map (lambda (x) (translation-of x senv)) exp1*)
        (map (lambda (x) (translation-of x senv)) exp2*)))
    (var-exp (var)
      (nameless-var-exp
        (apply-senv senv var)))
    (let-exp (var exp1 body)
      (nameless-let-exp
        (translation-of exp1 senv)
        (translation-of body
          (extend-senv var senv))))
    (proc-exp (var body)
      (nameless-proc-exp
        (translation-of body
          (extend-senv var senv))))
    (call-exp (rator rand)
      (call-exp (translation-of rator senv)
                (translation-of rand senv)))
    (list-exp (exp*)
      (list-exp (map (lambda (x) (translation-of x senv)) exp*)))
    (unpack-exp (var* exp body)
      (nameless-unpack-exp
         (length var*)
         (translation-of exp senv)
         (translation-of body (extend-senv* var* senv))))
    (else
      report-invalid-source-expression exp)))

(define (report-invalid-source-expression exp)
  (eopl:error 'translation-of "Invalid source expression ~s" exp))


(define (empty-senv) '())
(define extend-senv cons)
(define extend-senv* append)
(define (apply-senv senv var)
  (cond ((null? senv)
         (report-unbound-var var))
        ((eqv? var (car senv))
         0)
        (else
         (+ 1 (apply-senv (cdr senv) var)))))

(define (report-unbound-var var)
  (eopl:error 'apply-senv "Unbound variable ~s" var))


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
    (cond-exp (exp1* exp2*)
      (value-of-cond exp1* exp2* env))
    (call-exp (rator rand)
      (let ((proc (expval->proc (value-of rator env)))
            (arg (value-of rand env)))
        (apply-procedure proc arg)))
    (list-exp (exp*)
      (map (lambda (x) (value-of x env)) exp*))
    (nameless-var-exp (n) (apply-nameless-env env n))
    (nameless-let-exp (exp1 body)
      (let ((val (value-of exp1 env)))
        (value-of body
          (extend-nameless-env val env))))
    (nameless-proc-exp (body)
      (proc-val (procedure body env)))
    (nameless-unpack-exp (n exp1 body)
      (let ((val (value-of exp1 env)))
        (if (eqv? n (length val))
            (value-of body (append val env))
            (report-unpack-mismatch n (length val)))))
    (else
      (report-invalid-translated-expression exp))))

(define (report-invalid-translated-expression exp)
  (eopl:error 'value-of "Invalid translated expression ~s" exp))

(define (value-of-cond exp1* exp2* env)
  (cond ((null? exp1*)
         (eopl:error 'value-of "Invalid translated expression ~s" exp)) 
        ((expval->bool (value-of (car exp1*) env))
         (value-of (car exp2*) env))
        (else
         (value-of-cond (cdr exp1*) (cdr exp2*) env))))


(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (list-val (lst (list-of expval?)))
  (proc-val (proc proc?)))

(define (make-val x)
  (cond ((integer? x) (num-val x))
        ((boolean? x) (bool-val x))
        ((list? x) (list-val (map make-val x)))))

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

(define (expval->list val)
  (cases expval val
    (list-val (lst) lst)
    (else (report-expval-extractor-error 'list val))))

(define (report-expval-extractor-error kind val)
  (eopl:error kind "expected ~s but got value ~s" kind val))

(define (report-unpack-mismatch n m)
  (eopl:error 'value-of-unpack "wrong number of values to unpack ~s / ~s" n m))


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
  "cond zero?(0) ==> 42 end"
  (make-val 42))

(assert-eval
  "cond zero?(2) ==> 2 zero?(0) ==> 1 zero?(1) ==> 0 end"
  (make-val 1))

(assert-eval
  "let u = 7
   in unpack x y = list(u,3)
      in -(x,y)"
  (make-val 4))

(newline)
(display "OK")
