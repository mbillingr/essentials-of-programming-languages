#lang eopl

; EXPLICIT-REFS lang with ...
;   - begin
;   - store-passing interpreter

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
      ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" identifier ")" expression)
      proc-exp)

    (expression
      ("(" expression expression ")")
      call-exp)

    (expression 
      ("newref" "(" expression ")")
      newref-exp)

    (expression 
      ("deref" "(" expression ")")
      deref-exp)

    (expression 
      ("setref" "(" expression "," expression ")")
      setref-exp)

    (expression 
      ("begin" expression (arbno expression) "end")
      begin-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (value-of-program (scan&parse source)))

(define-datatype answer answer?
  (an-answer
    (val expval?)
    (store store?)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
      (cases answer (value-of exp1 (init-env) (empty-store))
        (an-answer (val store)
          val)))))

(define (value-of exp env store)
  (newline)
  (display "value-of ")
  (display exp)
  (newline)
  (cases expression exp
    (const-exp (num) (an-answer (num-val num) store))
    (var-exp (var) (an-answer (apply-env env var) store))  ; the book uses apply-store here. Why?
    (diff-exp (exp1 exp2)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 store1)
          (cases answer (value-of exp2 env store1)
            (an-answer (val2 store2)
              (let ((num1 (expval->num val1))
                    (num2 (expval->num val2)))
                (an-answer (num-val (- num1 num2))
                           store2)))))))
    (zero?-exp (exp1)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 store1)
          (let ((num1 (expval->num val1)))
            (an-answer (if (zero? num1)
                           (bool-val #t)
                           (bool-val #f))
                       store1)))))
    (if-exp (exp1 exp2 exp3)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 store1)
          (if (expval->bool val1)
              (value-of exp2 env store1)
              (value-of exp3 env store1)))))
    (let-exp (var exp1 body)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 store1)
          (value-of body
                    (extend-env var val1 env)
                    store1))))
    (letrec-exp (proc-name* bound-var* proc-body* letrec-body)
      (value-of letrec-body 
                (extend-env-rec proc-name* bound-var* proc-body* env)
                store))
    (proc-exp (var body)
      (an-answer (proc-val (procedure var body env))
                 store))
    (call-exp (rator rand)
      (cases answer (value-of rator env store)
        (an-answer (procval store1)
          (cases answer (value-of rand env store1)
            (an-answer (arg store2)      
              (apply-procedure (expval->proc procval) arg store2))))))
    (newref-exp (exp1)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 store1)
          (newref store1 val1))))
    (deref-exp (exp1)
      (cases answer (value-of exp1 env store)
        (an-answer (v1 new-store)
          (let ((ref1 (expval->ref v1)))
            (an-answer (deref new-store ref1) new-store)))))
    (setref-exp (exp1 exp2)
      (cases answer (value-of exp1 env store)
        (an-answer (refval store1)
          (cases answer (value-of exp2 env store1)
            (an-answer (val2 store2)
              (an-answer (num-val 23) 
                         (setref store2 (expval->ref refval) val2)))))))
    (begin-exp (first rest)
      (let ((ans1 (value-of first env store)))
        (if (null? rest)
            ans1
            (cases answer ans1
              (an-answer (val1 store1)
                (value-of (begin-exp (car rest) (cdr rest)) 
                          env
                          store1))))))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (ref-val (ref reference?)))

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

(define (expval->ref val)    
  (cases expval val
    (ref-val (ref) ref)
    (else (report-expval-extractor-error 'ref val))))

(define (report-expval-extractor-error kind val)
  (eopl:error kind "expected ~s but got value ~s" kind val))


(define (proc? val)
  (procedure? val))

(define (procedure var body env)
  (lambda (val store)
    (value-of body (extend-env var val env) store)))

(define (apply-procedure proc1 val store)
  (proc1 val store))


(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val (lambda (x) #t)) (env environment?)))

(define (extend-env-rec p-name* b-var* body* saved-env)
  (let* ((vec* (map (lambda (_) (make-vector 1)) p-name*))
         (new-env (extend-env* p-name* vec* saved-env)))
    (set-env-rec! b-var* body* vec* new-env)
    new-env))

(define (extend-env* name* val* saved-env)
  (if (null? name*)
      saved-env
      (extend-env* (cdr name*) (cdr val*) 
        (extend-env (car name*) (car val*) saved-env))))

(define (set-env-rec! b-var* body* vec* env)
  (if (null? b-var*)
      'done
      (begin
        (vector-set! (car vec*) 0
          (proc-val (procedure (car b-var*) (car body*) env)))
        (set-env-rec! (cdr b-var*) (cdr body*) (cdr vec*) env))))

(define (apply-env env search-var)
  (cases environment env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env (var val parent) 
      (if (eqv? var search-var)
        (if (vector? val)
            (vector-ref val 0) 
            val)
        (apply-env parent search-var)))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))

(define (store? x)
  ((list-of expval?) x))

(define (empty-store) '())

(define (reference? v)
  (integer? v))

(define (newref store val)
  (let ((next-ref (length store)))
    (an-answer (ref-val next-ref) (append store (list val)))))

(define (deref store ref)
  (list-ref store ref))

(define (setref store ref val)
  (cond
    ((null? store)
     (report-invalid-reference ref store))
    ((zero? ref)
     (cons val (cdr store)))
    (else
      (cons (car store)
            (setref (cdr store) (- ref 1) val)))))

(define (report-invalid-reference ref store)
  (eopl:error 'setref "Invalid reference ~s in ~s" ref store))


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
  "let x = 123 in (proc (x) x 42)"
  (num-val 42))

(assert-eval
  "letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in (double 6)"
  (num-val 12))

(assert-eval
  "letrec 
     odd(x) = if zero?(x) then 0 else (even -(x,1))
     even(x) = if zero?(x) then 1 else (odd -(x,1))
   in (odd 13)"
  (num-val 1))

(assert-eval
  "let x = newref(1)
   in begin
        setref(x,2)
        deref(x)
      end"
  (num-val 2))

(newline)
(display "OK")
