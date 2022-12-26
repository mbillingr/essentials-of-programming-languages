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

    (decl
      ("opaque" identifier)
      opaque-type-decl)
      
    (decl
      ("transparent" identifier "=" type)
      transparent-type-decl)

    (module-body
      ("["  (arbno definition) "]")
      defns-module-body)

    (definition
      (identifier "=" expression)
      val-defn)

    (definition
      ("type" identifier "=" type)
      type-defn)


    (type
      ("int")
      int-type)

    (type
      ("bool")
      bool-type)

    (type
      ("(" type "->" type ")")
      proc-type)

    (type
      (identifier)
      named-type)

    (type
      ("from" identifier "take" identifier)
      qualified-type)


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
                        (extend-tenv-with-module m-name 
                          (expand-iface m-name expected-iface tenv) 
                          tenv)))
                  (add-module-defns-to-tenv
                    (cdr defns) new-tenv))
                (report-module-doesnt-satisfy-iface
                  m-name expected-iface actual-iface)))))))

(define (expand-iface m-name iface tenv)
  (cases interface iface
    (simple-iface (decls)
      (simple-iface
        (expand-decls m-name decls tenv)))))

(define (expand-decls m-name decls internal-tenv)
  (if (null? decls)
      '()
      (cases decl (car decls)
        (opaque-type-decl (t-name)
          (let ((expanded-type (qualified-type m-name t-name)))
            (let ((new-env (extend-tenv-with-type t-name expanded-type internal-tenv)))
              (cons (transparent-type-decl t-name expanded-type)
                    (expand-decls m-name (cdr decls) new-env)))))
        (transparent-type-decl (t-name ty)
          (let ((new-env (extend-tenv-with-expanded-type t-name ty internal-tenv)))
            (let ((expanded-type (apply-tenv new-env t-name)))
              (cons (transparent-type-decl t-name expanded-type)
                    (expand-decls m-name (cdr decls) new-env)))))
        (val-decl (var-name ty)
          (let ((expanded-type (expand-type ty internal-tenv)))
            (cons (val-decl var-name expanded-type)
                  (expand-decls m-name (cdr decls) internal-tenv)))))))

(define (report-module-doesnt-satisfy-iface m-name expected-iface actual-iface)
  (eopl:error 
    'add-module-defns-to-tenv 
    "module ~s body ~s does not match interface ~s" 
    m-name actual-iface expected-iface))

(define (interface-of m-body tenv)
  (cases module-body m-body
    (defns-module-body (defns)
      (simple-iface
        (defns-to-decls defns tenv)))))

(define (defns-to-decls defns tenv)
  (if (null? defns)
      '()
      (cases definition (car defns)
        (val-defn (var-name exp)
          (let ((ty (type-of exp tenv)))
            (let ((new-env (extend-tenv var-name ty tenv)))
              (cons (val-decl var-name ty)
                    (defns-to-decls (cdr defns) new-env)))))
        (type-defn (name ty)
          (let ((new-env
                  (extend-tenv-with-expanded-type name ty tenv)))
            (cons (transparent-type-decl name ty)
                  (defns-to-decls (cdr defns) new-env)))))))

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
            (and (<:-decl (car decls1) (car decls2) tenv)
                 (<:-decls (cdr decls1) (cdr decls2)
                           (extend-tenv-with-decl (car decls1) tenv)))
            (<:-decls (cdr decls1) decls2 
                      (extend-tenv-with-decl (car decls1) tenv)))))))

(define (extend-tenv-with-decl decl1 tenv)
  (cases decl decl1
    (val-decl (name ty) tenv)
    (transparent-type-decl (name ty)
      (extend-tenv-with-expanded-type name ty tenv))
    (opaque-type-decl (name)
      (extend-tenv-with-expanded-type
        name
        (qualified-type (fresh-module-name '%unknown) name)
        tenv))))

(define fresh-module-name
  (let ((count 0))
    (lambda (name)
      (set! count (+ count 1))      
      (string->symbol
        (string-append 
           (symbol->string name)
           "-"
           number->string count)))))

(define (<:-decl decl1 decl2 tenv)
  (or (and (val-decl? decl1)
           (val-decl? decl2)
           (equiv-type? 
             (decl->type decl1)
             (decl->type decl2) tenv))
      (and (transparent-type-decl? decl1)
           (transparent-type-decl? decl2)
           (equiv-type?
             (decl->type decl1)
             (decl->type decl2) tenv))
      (and (transparent-type-decl? decl1)
           (opaque-type-decl? decl2))
      (and (opaque-type-decl? decl1)
           (opaque-type-decl? decl2))))

(define (equiv-type? ty1 ty2 tenv)
  (equal? (expand-type ty1 tenv)
          (expand-type ty2 tenv)))

(define (val-decl? decl1)
  (cases decl decl1
    (val-decl (name ty)
      #t)
    (else 
      #f)))

(define (transparent-type-decl? decl1)
  (cases decl decl1
    (transparent-type-decl (name ty)
      #t)
    (else 
      #f)))

(define (opaque-type-decl? decl1)
  (cases decl decl1
    (opaque-type-decl (name)
      #t)
    (else 
      #f)))

(define (decl->name decl1)
  (cases decl decl1
    (val-decl (name ty)
      name)
    (transparent-type-decl (name ty)
      name)
    (opaque-type-decl (name)
      name)))

(define (decl->type decl1)
  (cases decl decl1
    (val-decl (name ty)
      ty)
    (transparent-type-decl (name ty)
      ty)
    (else
      (eopl:error 'decl->type "called on an opaque type"))))

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
        (type-of body (extend-tenv-expanded var ty1 tenv))))
    (proc-exp (var var-type body)
      (let ((result-type (type-of body (extend-tenv-expanded var var-type tenv))))
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
              (extend-tenv-expanded p-name
                (proc-type b-var-type p-result-type)
                tenv)))
        (let ((p-body-type
                (type-of p-body
                  (extend-tenv-expanded b-var b-var-type tenv-for-letrec-body))))
          (check-equal-type! p-body-type p-result-type p-body)
          (type-of letrec-body tenv-for-letrec-body))))
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
            (type-to-external-form res-type)))
    (named-type (name)
      name)
    (qualified-type (m-name t-name)
      (list 'from m-name 'take t-name))))

(define (expand-type ty tenv)
  (cases type ty
    (int-type () (int-type))
    (bool-type () (bool-type))
    (proc-type (arg-type result-type)
      (proc-type
        (expand-type arg-type tenv)
        (expand-type result-type tenv)))
    (named-type (name)
      (lookup-type-in-tenv tenv name))
    (qualified-type (m-name t-name)
      (lookup-qualified-type-in-tenv m-name t-name tenv))))


(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var symbol?) (ty type?) (env tenvironment?))
  (extend-tenv-with-module (name symbol?) (interface interface?) (saved-tenv tenvironment?))
  (extend-tenv-with-type (name symbol?) (type type?) (saved-tenv tenvironment?)))

(define (extend-tenv-expanded var ty saved-tenv)
  (extend-tenv var (expand-type ty saved-tenv) saved-tenv))

(define (extend-tenv-with-expanded-type name type saved-tenv)
  (extend-tenv-with-type name (expand-type type saved-tenv) saved-tenv))

(define (apply-tenv env search-var)
  (cases tenvironment env
    (empty-tenv () 
      (report-no-binding-found search-var))
    (extend-tenv (var ty parent) 
      (if (eqv? var search-var) 
        ty
        (apply-tenv parent search-var)))
    (extend-tenv-with-module (m-name iface saved-tenv)
      (apply-tenv saved-tenv search-var))
    (extend-tenv-with-type (name ty saved-env)
      (apply-tenv saved-env search-var))))

(define (lookup-qualified-var-in-tenv m-name var-name tenv)
  (let ((iface (lookup-module-name-in-tenv tenv m-name)))
    (cases interface iface
      (simple-iface (decls)
        (lookup-variable-name-in-decls var-name decls)))))

(define (lookup-qualified-type-in-tenv m-name t-name tenv)
  (let ((iface (lookup-module-name-in-tenv tenv m-name)))
    (cases interface iface
      (simple-iface (decls)
        (lookup-variable-name-in-decls t-name decls)))))  ; TODO - is this correct?

(define (lookup-module-name-in-tenv tenv m-search-name)
  (cases tenvironment tenv
    (empty-tenv ()
      (report-no-binding-found m-search-name))
    (extend-tenv (var ty saved-tenv)
      (lookup-module-name-in-tenv saved-tenv m-search-name))
    (extend-tenv-with-module (m-name iface saved-tenv)
      (if (eqv? m-name m-search-name)
          iface
          (lookup-module-name-in-tenv saved-tenv m-search-name)))
    (extend-tenv-with-type (name ty saved-tenv)
      (lookup-module-name-in-tenv saved-tenv m-search-name))))

(define (lookup-type-in-tenv tenv search-name)
  (cases tenvironment tenv
    (empty-tenv ()
      (report-no-binding-found search-name))
    (extend-tenv (var ty saved-tenv)
      (lookup-type-in-tenv saved-tenv search-name))
    (extend-tenv-with-module (m-name iface saved-tenv)
      (lookup-type-in-tenv saved-tenv search-name))
    (extend-tenv-with-type (name ty saved-env)
      (if (eqv? name search-name)
          ty
          (lookup-type-in-tenv saved-env search-name)))))

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
        (defns-to-env defns env)))))

(define (defns-to-env defns env)
  (if (null? defns)
      (empty-env)
      (cases definition (car defns)
        (val-defn (var exp)
          (let ((val (value-of exp env)))
            (let ((new-env (extend-env var val env)))
              (extend-env var val
                (defns-to-env (cdr defns) new-env)))))
        (type-defn (type-name type)
          (defns-to-env (cdr defns) env)))))

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
  "module m
    interface [opaque t z: t s: (t -> t)]
    body [
      type t = int
      z = 0
      s = proc (n : t) -(n,1)
    ]
  let z = from m take z
  in let s = from m take s
  in (s (s z))"
  (qualified-type 'm 't) -2)

(newline)
(display "OK")
(newline)