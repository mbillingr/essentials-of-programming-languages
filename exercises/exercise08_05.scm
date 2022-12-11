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
  '((program 
      ((arbno module-definition) expression) 
      a-program)

    (module-definition
      ("module" identifier "interface" interface "body" module-body)
      a-module-definition)

    (interface
      ("[" (arbno decl) "]")
      simple-iface)

    (decl
      (identifier ":" type)
      val-decl)

    (module-body
      ("["  (arbno definition) "]")
      defns-module-body)

    (module-body
      ("let"  (arbno identifier "=" expression) "in" module-body)
      let-module-body)

    (module-body
      ("letrec" type identifier "(" identifier ":" type ")" "=" expression "in" module-body)
      letrec-module-body)

    (definition
      (identifier "=" expression)
      val-defn)


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
      ("from" identifier "take" identifier)
      qualified-var-exp)

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
    (a-program (module-defns body) 
      (type-of body
        (add-module-defns-to-tenv module-defns (empty-tenv))))))

(define (add-module-defns-to-tenv defns tenv)
  (if (null? defns)
      tenv
      (cases module-definition (car defns)
        (a-module-definition (m-name expected-iface m-body)
          (let ((actual-iface (interface-of m-body tenv)))
            (if (<:-iface actual-iface expected-iface tenv)
                (let ((new-tenv
                        (extend-tenv-with-module m-name expected-iface tenv)))
                  (add-module-defns-to-tenv
                    (cdr defns) new-tenv))
                (report-module-doesnt-satisfy-iface
                  m-name expected-iface actual-iface)))))))

(define (report-module-doesnt-satisfy-iface m-name expected-iface actual-iface)
  (eopl:error 
    'add-module-defns-to-tenv 
    "module ~s body ~s does not match interface ~s" 
    m-name actual-iface expected-iface))

(define (interface-of m-body tenv)
  (cases module-body m-body
    (defns-module-body (defns)
      (simple-iface
        (defns-to-decls defns tenv)))
    (let-module-body (vars vals let-body)
      (interface-of let-body
        (extend-tenv* vars 
          (map (lambda (exp) (type-of exp tenv)) vals)
          tenv)))
    (letrec-module-body (a b c d e let-body)
      (interface-of let-body
        (extend-tenv-rec a b c d e tenv)))))

(define (defns-to-decls defns tenv)
  (if (null? defns)
      '()
      (cases definition (car defns)
        (val-defn (var-name exp)
          (let ((ty (type-of exp tenv)))
            (cons (val-decl var-name ty)
                  (defns-to-decls
                    (cdr defns)
                    (extend-tenv var-name ty tenv))))))))

(define (<:-iface iface1 iface2 tenv)
  (cases interface iface1
    (simple-iface (decls1)
      (cases interface iface2
        (simple-iface (decls2)
          (<:-decls decls1 decls2 tenv))))))

(define (<:-decls decls1 decls2 tenv)
  (cond
    ((null? decls2) #t)
    ((null? decls1) #f)
    (else
      (let ((name1 (decl->name (car decls1)))
            (name2 (decl->name (car decls2))))
        (if (eqv? name1 name2)
            (and (equal? (decl->type (car decls1))
                         (decl->type (car decls2)))
                 (<:-decls (cdr decls1) (cdr decls2) tenv))
            (<:-decls (cdr decls1) decls2 tenv))))))

(define (decl->name decl1)
  (cases decl decl1
    (val-decl (name ty)
      name)))

(define (decl->type decl1)
  (cases decl decl1
    (val-decl (name ty)
      ty)))

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
      (type-of letrec-body
        (extend-tenv-rec p-result-type p-name b-var b-var-type p-body tenv)))
    (qualified-var-exp (m-name var)
      (lookup-qualified-var-in-tenv m-name var tenv))))

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
  (extend-tenv (var symbol?) (ty type?) (env tenvironment?))
  (extend-tenv-with-module (name symbol?) (interface interface?) (saved-tenv tenvironment?)))

(define (extend-tenv* vars tys tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars) (cdr tys)
        (extend-tenv (car vars) (car tys) tenv))))

(define (extend-tenv-rec p-result-type p-name b-var b-var-type p-body tenv)
  (let ((tenv-for-letrec-body
          (extend-tenv p-name
            (proc-type b-var-type p-result-type)
            tenv)))
    (let ((p-body-type
            (type-of p-body
              (extend-tenv b-var b-var-type tenv-for-letrec-body))))
      (check-equal-type! p-body-type p-result-type p-body)
      tenv-for-letrec-body)))

(define (apply-tenv env search-var)
  (cases tenvironment env
    (empty-tenv () 
      (report-no-binding-found search-var))
    (extend-tenv (var ty parent) 
      (if (eqv? var search-var) 
        ty
        (apply-tenv parent search-var)))
    (extend-tenv-with-module (m-name iface saved-tenv)
      (apply-tenv saved-tenv search-var))))

(define (lookup-qualified-var-in-tenv m-name var-name tenv)
  (let ((iface (lookup-module-name-in-tenv tenv m-name)))
    (cases interface iface
      (simple-iface (decls)
        (lookup-variable-name-in-decls var-name decls)))))

(define (lookup-module-name-in-tenv tenv m-search-name)
  (cases tenvironment tenv
    (empty-tenv ()
      (report-no-binding-found m-search-name))
    (extend-tenv (var ty saved-tenv)
      (lookup-module-name-in-tenv saved-tenv m-search-name))
    (extend-tenv-with-module (m-name iface saved-tenv)
      (if (eqv? m-name m-search-name)
          iface
          (lookup-module-name-in-tenv saved-tenv m-search-name)))))

(define (lookup-variable-name-in-decls var-name decls)
  (if (null? decls)
      (report-no-binding-found var-name)
      (if (eqv? (decl->name (car decls))
                var-name)
          (decl->type (car decls))
          (lookup-variable-name-in-decls var-name (cdr decls)))))


(define (run source)
  (value-of-program (scan&parse source)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (m-defns body)
      (value-of body
        (add-module-defns-to-env m-defns (empty-env))))))

(define (add-module-defns-to-env defns env)
  (if (null? defns)
      env
      (cases module-definition (car defns)
        (a-module-definition (m-name iface m-body)
          (add-module-defns-to-env
            (cdr defns)
            (extend-env-with-module
              m-name
              (value-of-module-body m-body env)
              env))))))

(define (value-of-module-body m-body env)
  (cases module-body m-body
    (defns-module-body (defns)
      (simple-module
        (defns-to-env defns env)))
    (let-module-body (vars vals let-body)
      (value-of-module-body let-body 
        (extend-env* 
          vars 
          (map (lambda (exp) (value-of exp env)) vals)
          env)))
    (letrec-module-body (tres p-name b-var tvar p-body letrec-body)
      (value-of-module-body letrec-body
        (extend-env-rec p-name b-var p-body env)))))

(define (defns-to-env defns env)
  (if (null? defns)
      (empty-env)
      (cases definition (car defns)
        (val-defn (var exp)
          (let ((val (value-of exp env)))
            (let ((new-env (extend-env var val env)))
              (extend-env var val
                (defns-to-env (cdr defns) new-env))))))))

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
        (apply-procedure proc arg)))
    (qualified-var-exp (m-name var)
      (lookup-qualified-var-in-env m-name var env))))

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


(define-datatype typed-module typed-module?
  (simple-module
    (bindings environment?)))

(define (lookup-qualified-var-in-env m-name var-name env)
  (let ((m-val (lookup-module-name-in-env m-name env)))
    (cases typed-module m-val
      (simple-module (bindings)
        (apply-env bindings var-name)))))

(define (lookup-module-name-in-env m-search-name env)
  (cases environment env
    (empty-env () 
      (report-no-binding-found m-search-name))
    (extend-env (var val saved-env) 
      (lookup-module-name-in-env m-search-name saved-env))
    (extend-env-rec (p-name b-var p-body saved-env)
      (lookup-module-name-in-env m-search-name saved-env))
    (extend-env-with-module (m-name m-val saved-env)
      (if (eqv? m-name m-search-name)
          m-val
          (lookup-module-name-in-env m-search-name saved-env)))))
  

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
  (extend-env-rec (p-name symbol?) (b-var symbol?) (body expression?) (env environment?))
  (extend-env-with-module
    (m-name symbol?)
    (m-val typed-module?)
    (saved-env environment?)))

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
    (extend-env-rec (p-name b-var p-body parent)
      (if (eqv? p-name search-var)
          (proc-val (procedure b-var p-body env))
          (apply-env parent search-var)))
    (extend-env-with-module (m-name m-val saved-env)
      (apply-env saved-env search-var))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))


(define (assert-eval src expected-ty expected-val)
  (display ".")
  (let ((ty (check src)))
    (check-equal-type! ty expected-ty src)
    (let ((val (expval->scmval (run src))))
      (if (eqv? val expected-val)
          'ok
          (eopl:error 'assert-eval "~s evaluated to ~s but expected ~s" src val expected-val)))))

(define (expval->scmval val)
  (cases expval val
    (num-val (x) x)
    (bool-val (x) x)
    (proc-val (x) x)))


(assert-eval 
  "42" 
  (int-type) 42)

(assert-eval
  "-(8,5)"
  (int-type) 3)

(assert-eval
  "zero? (0)"
  (bool-type) #t)

(assert-eval
  "zero? (5)"
  (bool-type) #f)

(assert-eval
  "if zero? (0) then 1 else 2"
  (int-type) 1)

(assert-eval
  "let x = 123 in x"
  (int-type) 123)

(assert-eval
  "letrec int double(x : int) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in (double 6)"
  (int-type) 12)

(assert-eval
  "module m1
    interface [a: int b: int c: int]
    body [a=33 b=44 c=55]
  module m2
    interface [a: int b: int]
    body [a=66 b=77]
  let z = 99
  in -(z, -(from m1 take a, from m2 take a))"
  (int-type) 132)

(assert-eval
  "module numbers
    interface 
      [even : (int -> bool)]
    body 
      let 
        true = zero?(0)
        false = zero?(1)
      in letrec
        bool local-even (x : int) = 
          if zero?(x) 
          then true 
          else if zero?(-(x,1))
               then false
               else (local-even -(x,2))
      in [even = local-even]
  (from numbers take even 123)"
  (bool-type) #f)


(newline)
(display "OK")
(newline)