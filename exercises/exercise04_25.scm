#lang eopl

; IMPLICIT-REFS lang 
;  - statement oriented
;  - read statements
;  - do-while statements
;  - initialized var blocks (let* style)

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))
      
(define the-grammar
  '((program (statement) a-program)

    (statement
      ("halt" expression)
      halt-stmt)
    (statement
      ("print" expression)
      print-stmt)
    (statement
      (identifier "=" expression)
      assign-stmt)
    (statement
      ("{" (separated-list statement ";") "}")
      block-stmt)
    (statement
      ("if" expression statement statement)
      if-stmt)
    (statement
      ("while" expression statement)
      while-stmt)
    (statement
      ("do-while" statement expression)
      dowhile-stmt)
    (statement
      ("var" (separated-list identifier "=" expression ",") ";" statement)
      var-stmt)
    (statement
      ("read" identifier)
      read-stmt)

    (expression (number) const-exp)
    (expression
      ("-" "(" expression "," expression ")")
      diff-exp)
    (expression
      ("*" "(" expression "," expression ")")
      mul-exp)
    
    (expression
      ("zero?" "(" expression ")")
      zero?-exp)
    
    (expression
      ("not" "(" expression ")")
      not-exp)

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
      ("begin" expression (arbno expression) "end")
      begin-exp)

    (expression
      ("set" identifier "=" expression)
      assign-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (run-program (scan&parse source)))

(define (run-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (stmt)
      (execute stmt (init-env)))))

(define (execute stmt env)
  (cases statement stmt
    (halt-stmt (exp) (value-of exp env))
    (print-stmt (exp) (begin (display (value-of exp env))
                             (newline)
                             'nothing))
    (assign-stmt (var exp1)
      (begin
        (setref!
          (apply-env env var)
          (value-of exp1 env))
        'nothing))
    (block-stmt (stmt*)
      (if (null? stmt*)
          'nothing
          (if (null? (cdr stmt*))
              (execute (car stmt*) env)
              (begin (execute (car stmt*) env)
                     (execute (block-stmt (cdr stmt*)) env)))))
    (if-stmt (exp1 stmt2 stmt3)
      (if (expval->bool (value-of exp1 env))
          (execute stmt2 env)
          (execute stmt3 env)))
    (while-stmt (exp1 body)
      (if (expval->bool (value-of exp1 env))
          (begin
            (execute body env)
            (execute (while-stmt exp1 body) env))
          'nothing))
    (dowhile-stmt (body exp1)
      (begin
        (execute body env)
        (if (expval->bool (value-of exp1 env))
            (execute (while-stmt exp1 body) env)
            'nothing)))
    (var-stmt (var* exp* body)
      (if (null? var*)
          (execute body env)
          (execute (var-stmt (cdr var*) (cdr exp*) body)
                   (extend-env (car var*) 
                               (newref (value-of (car exp*) env))
                               env))))
    (read-stmt (var)
      (begin
        (setref!
          (apply-env env var)
          (num-val (read)))
        'nothing))))

(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (var-exp (var) (deref (apply-env env var)))
    (diff-exp (exp1 exp2)
      (let* ((val1 (value-of exp1 env))
             (val2 (value-of exp2 env))
             (num1 (expval->num val1))
             (num2 (expval->num val2)))
        (num-val (- num1 num2))))
    (mul-exp (exp1 exp2)
      (let* ((val1 (value-of exp1 env))
             (val2 (value-of exp2 env))
             (num1 (expval->num val1))
             (num2 (expval->num val2)))
        (num-val (* num1 num2))))
    (zero?-exp (exp1)
      (let* ((val1 (value-of exp1 env))
             (num1 (expval->num val1)))
        (if (zero? num1)
            (bool-val #t)
            (bool-val #f))))
    (not-exp (exp1)
      (if (expval->bool (value-of exp1 env))
          (bool-val #f)
          (bool-val #t)))
    (if-exp (exp1 exp2 exp3)
      (let ((val1 (value-of exp1 env)))
        (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))
    (let-exp (var exp1 body)
      (let ((val1 (value-of exp1 env)))
        (value-of body
          (extend-env var (newref val1) env))))
    (letrec-exp (proc-name* bound-var* proc-body* letrec-body)
      (value-of letrec-body 
                (extend-env-rec proc-name* bound-var* proc-body* env)))
    (proc-exp (var body)
      (proc-val (procedure var body env)))
    (call-exp (rator rand)
      (let ((proc (expval->proc (value-of rator env)))
            (arg (value-of rand env)))
        (apply-procedure proc arg)))
    (begin-exp (first rest)
      (let ((val1 (value-of first env)))
        (if (null? rest)
            val1
            (value-of (begin-exp (car rest) (cdr rest)) env))))
    (assign-exp (var exp1)
      (begin
        (setref!
          (apply-env env var)
          (value-of exp1 env))
        (num-val 27)))))

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
  (lambda (val)
    (value-of body (extend-env var (newref val) env))))

(define (apply-procedure proc1 val)
  (proc1 val))


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
          (newref (proc-val (procedure (car b-var*) (car body*) env))))
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


(define (empty-store) '())

(define the-store 'uninitialized)

(define (get-store) the-store)

(define (initialize-store!)
  (set! the-store (empty-store)))

(define (reference? v)
  (integer? v))

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store
    (letrec
      ((setref-inner
         (lambda (store1 ref1)
           (cond
             ((null? store1)
              (report-invalid-reference ref the-store))
             ((zero? ref1)
              (cons val (cdr store1)))
             (else
               (cons (car store1)
                     (setref-inner
                        (cdr store1) (- ref1 1))))))))
      (setref-inner the-store ref))))

(define (report-invalid-reference ref store)
  (eopl:error 'setref! "Invalid reference ~s in ~s" ref store))


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
  "halt 42" 
  (num-val 42))

(assert-eval
  "halt -(8,5)"
  (num-val 3))

(assert-eval
  "halt zero? (0)"
  (bool-val #t))

(assert-eval
  "halt zero? (5)"
  (bool-val #f))

(assert-eval
  "halt if zero? (0) then 1 else 2"
  (num-val 1))

(assert-eval
  "halt if zero? (9) then 1 else 2"
  (num-val 2))

(assert-eval
  "halt let x = 123 in x"
  (num-val 123))

(assert-eval
  "halt let x = 123 in (proc (x) x 42)"
  (num-val 42))

(assert-eval
  "halt letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in (double 6)"
  (num-val 12))

(assert-eval
  "halt letrec 
     odd(x) = if zero?(x) then 0 else (even -(x,1))
     even(x) = if zero?(x) then 1 else (odd -(x,1))
   in (odd 13)"
  (num-val 1))

(assert-eval
  "halt let x = 123 in begin set x = 42 x end"
  (num-val 42))

(assert-eval "{}" 'nothing)
(assert-eval "{halt 42}" (num-val 42))
(assert-eval "var x = 0; {x = 42; halt x}" (num-val 42))
(assert-eval "if zero?(0) halt 5 halt 9" (num-val 5))
(assert-eval "halt not(zero?(0))" (bool-val #f))
(assert-eval "var x = 0; {do-while x = 1 zero?(99); halt x}" (num-val 1))
(assert-eval "var n=5, fact=1; {
                while not(zero?(n)) {
                  fact = *(fact,n); 
                  n = -(n,1)
                }; 
                halt fact
              }" (num-val 120))


(newline)
(display "OK")
