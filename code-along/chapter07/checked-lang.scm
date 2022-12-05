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

    (type
      ("int")
      int-type)

    (type
      ("bool")
      bool-type)

    (type
      ("(" type "->" type ")")
      proc-type)

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
      ("letrec" type identifier "(" identifier ":" type ")" "=" expression "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" identifier ":" type ")" expression)
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


(define (check source)
  (type-of-program (scan&parse source)))

(define (type-of-program pgm)
  (cases program pgm
    (a-program (exp1) (type-of exp1 (empty-tenv)))))

(define (type-of exp tenv)
  (cases expression exp
    (const-exp (num) (int-type))
    (var-exp (var) (apply-tenv tenv var))
    (diff-exp (exp1 exp2)
      (let ((ty1 (type-of exp1 tenv))
            (ty2 (type-of exp2 tenv)))
        (check-equal-type! ty1 (int-type) exp1)
        (check-equal-type! ty2 (int-type) exp2)
        (int-type)))
    (zero?-exp (exp1)
      (let ((ty1 (type-of exp1 tenv)))
        (check-equal-type! ty1 (int-type) exp1)
        (bool-type)))
    (if-exp (exp1 exp2 exp3)
      (let ((ty1 (type-of exp1 tenv))
            (ty2 (type-of exp2 tenv))
            (ty3 (type-of exp3 tenv)))
        (check-equal-type! ty1 (bool-type) exp1)
        (check-equal-type! ty2 ty3 exp2)
        ty2))
    (let-exp (var exp1 body)
      (let ((ty1 (type-of exp1 tenv)))
        (type-of body (extend-tenv var ty1 tenv))))
    (proc-exp (var var-type body)
      (let ((result-type (type-of body (extend-tenv var var-type tenv))))
        (proc-type var-type result-type)))
    (call-exp (rator rand)
      (let ((rator-type (type-of rator tenv))
            (rand-type  (type-of rand tenv)))
        (cases type rator-type
          (proc-type (arg-type result-type)
            (begin
              (check-equal-type! arg-type rand-type rand)
              result-type))
          (else 
            (report-rator-not-a-proc-type rator-type rator)))))
    (letrec-exp (p-result-type p-name b-var b-var-type p-body letrec-body)
      (let ((tenv-for-letrec-body
              (extend-tenv p-name
                (proc-type b-var-type p-result-type)
                tenv)))
        (let ((p-body-type
                (type-of p-body
                  (extend-tenv b-var b-var-type tenv-for-letrec-body))))
          (check-equal-type! p-body-type p-result-type p-body)
          (type-of letrec-body tenv-for-letrec-body))))))

(define (report-rator-not-a-proc-type ty expr)
  (eopl:error 'type-of "expected a proc type but ~s is a ~s" ty expr))

(define (check-equal-type! ty1 ty2 exp)
  (if (equal? ty1 ty2)
      #t
      (report-unequal-types ty1 ty2 exp))) 

(define (report-unequal-types ty1 ty2 exp)
  (eopl:error 'check-equal-type!
    "Types didn't match: ~s != ~a in ~%~a"
    (type-to-external-form ty1)
    (type-to-external-form ty2)
    exp))

(define (type-to-external-form ty)
  (cases type ty
    (int-type () 'int)
    (bool-type () 'bool)
    (proc-type (arg-type res-type)
      (list (type-to-external-form arg-type)
            '->
            (type-to-external-form res-type)))))


(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var symbol?) (ty type?) (env tenvironment?)))
  ;(extend-env-rec (p-name symbol?) (b-var symbol?) (body expression?) (env environment?)))

(define (apply-tenv env search-var)
  (cases tenvironment env
    (empty-tenv () 
      (report-no-binding-found search-var))
    (extend-tenv (var ty parent) 
      (if (eqv? var search-var) 
        ty
        (apply-tenv parent search-var)))))
    ;(extend-env-rec (p-name b-var p-body parent)
    ;  (if (eqv? p-name search-var)
    ;      (proc-val (procedure b-var p-body env))
    ;      (apply-env parent search-var)))))


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
    (letrec-exp (tres proc-name bound-var tvar proc-body letrec-body)
      (value-of letrec-body 
                (extend-env-rec proc-name bound-var proc-body env)))
    (proc-exp (var tvar body)
      (proc-val (procedure var body env)))
    (call-exp (rator rand)
      (let ((proc (expval->proc (value-of rator env)))
            (arg (value-of rand env)))
        (apply-procedure proc arg)))))

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
  (lambda (val)
    (value-of body (extend-env var val env))))

(define (apply-procedure proc1 val)
  (proc1 val))


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


(define (assert-eval src expected-val)
  (display ".")
  (let ((val (check src)))
    (check-equal-type! val expected-val src)))


(assert-eval 
  "42" 
  (int-type))

(assert-eval
  "-(8,5)"
  (int-type))

(assert-eval
  "zero? (0)"
  (bool-type))

(assert-eval
  "zero? (5)"
  (bool-type))

(assert-eval
  "if zero? (0) then 1 else 2"
  (int-type))

(assert-eval
  "let x = 123 in x"
  (int-type))

(assert-eval
  "let x = 123 in proc (x : int) x"
  (proc-type (int-type) (int-type)))

(assert-eval
  "letrec int double(x : int) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in (double 6)"
  (int-type))

(newline)
(display "OK")
(newline)