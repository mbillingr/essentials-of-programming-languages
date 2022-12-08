#lang eopl

; INFERRED lang, with ...
;   - pairs
;   - multiple arguments, let, and letrec
;   - list type
;   - polymorphic functions (Algorithm W)


(define (dbg context x)
  (display "DBG: ")
  (display context)
  (display " ")
  (display x)
  (newline)
  x)


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
      ("(" (arbno type) "->" type ")")
      proc-type)

    (type
      ("pairof" type "*" type)
      pair-type)

    (type
      ("listof" type)
      list-type)

    (type
      ("%tvar-type" number)
      tvar-type)

    (optional-type
      ("?")
      no-type)

    (optional-type
      (type)
      a-type)

    (optional-type
      ("[" "?" "]")
      a-list-type)

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
      ("let" (arbno identifier "=" expression) "in" expression)
      let-exp)

    (expression
      ("letrec" (arbno optional-type identifier "(" (arbno identifier ":" optional-type) ")" "=" expression) "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" (arbno identifier ":" optional-type) ")" expression)
      proc-exp)

    (expression
      ("(" expression (arbno expression) ")")
      call-exp)

    (expression
      ("newpair" "(" expression "," expression ")")
      pair-exp)

    (expression
      ("unpair" identifier identifier "=" expression "in" expression)
      unpair-exp)

    (expression
      ("list" "(" (separated-list expression ",") ")")
      list-exp)

    (expression
      ("cons" "(" expression "," expression ")")
      cons-exp)

    (expression
      ("null?" "(" expression ")")
      null-exp)

    (expression
      ("emptylist")
      emptylist-exp)

    (expression
      ("first" "(" expression ")")
      first-exp)

    (expression
      ("rest" "(" expression ")")
      rest-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (check source)
  (type-of-program (scan&parse source)))

(define-datatype answer answer?
  (an-answer
    (ty type?)
    (subst substitution?)))

(define-datatype answer* answer*?
  (an-answer*
    (tys (list-of type?))
    (subst substitution?)))

(define (type-of-program pgm)
  (cases program pgm
    (a-program (exp1) 
      (cases answer (type-of exp1 (empty-tenv) (empty-subst))
        (an-answer (ty subst)
          (apply-subst-to-type ty subst))))))

(define (type-of exp tenv subst)
  (cases expression exp
    (const-exp (num) (an-answer (int-type) subst))
    (zero?-exp (exp1)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (let ((subst2 (unifier ty1 (int-type) subst1 exp)))
            (an-answer (bool-type) subst2)))))
    (diff-exp (exp1 exp2)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (let ((subst1 (unifier ty1 (int-type) subst1 exp1)))
            (cases answer (type-of exp2 tenv subst1)
              (an-answer (ty2 subst2)
                (let ((subst2 (unifier ty2 (int-type) subst2 exp2)))
                  (an-answer (int-type) subst2))))))))
    (if-exp (exp1 exp2 exp3)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst)
          (let ((subst (unifier ty1 (bool-type) subst exp1)))
            (cases answer (type-of exp2 tenv subst)
              (an-answer (ty2 subst)
                (cases answer (type-of exp3 tenv subst)
                  (an-answer (ty3 subst)
                    (let ((subst (unifier ty2 ty3 subst exp)))
                      (an-answer ty2 subst))))))))))
    (var-exp (var) (an-answer (apply-type-scheme (apply-tenv tenv var)) subst))
    (let-exp (vars exps body)
      (cases answer* (type-of* exps tenv subst)
        (an-answer* (tys subst)
          (type-of body
            (polymorphic-extend-tenv* vars           
              (map (lambda (t) (apply-subst-to-type t subst)) tys)
              tenv)
            subst))))
    (proc-exp (vars otypes body)
      (let ((var-types (map otype->type otypes)))
        (cases answer (type-of body
                               (extend-tenv* vars var-types tenv)
                               subst)
          (an-answer (body-type subst1)
            (an-answer
              (proc-type var-types body-type)
              subst1)))))
    (call-exp (rator rands)
      (let ((result-type (fresh-tvar-type)))
        (cases answer (type-of rator tenv subst)
          (an-answer (rator-type subst)
            (cases answer* (type-of* rands tenv subst)
              (an-answer* (rand-types subst)
                (let ((subst (unifier rator-type
                                      (proc-type rand-types result-type)
                                      subst exp)))
                  (an-answer result-type subst))))))))
    (letrec-exp (p-result-otypes p-names b-varss b-var-otypess p-bodies letrec-body)
      (let ((p-result-types (map otype->type p-result-otypes))
            (p-var-typess (map (lambda (tys) 
                                 (map otype->type tys)) 
                               b-var-otypess)))
        (let ((tenv-for-letrec-body
                (extend-tenv* p-names
                  (map (lambda (t) (apply-subst-to-type t subst))
                    (map proc-type p-var-typess p-result-types))
                  tenv)))
          (let ((subst (type-of-letrec 
                         p-result-types b-varss p-var-typess p-bodies subst tenv-for-letrec-body)))                      
            (type-of letrec-body
                     ; add a polymorphic binding of each function to the environment.
                     ; this is like wrapping a let around the letrec:
                     ;    let foo = letrec foo=... in foo in ...
                     (polymorphic-extend-tenv* p-names
                       (map (lambda (t) (apply-subst-to-type t subst))
                         (map (lambda (p) (apply-type-scheme (apply-tenv tenv-for-letrec-body p)))
                           p-names))
                       tenv-for-letrec-body)
                     subst)))))
    (pair-exp (exp1 exp2)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst)
          (cases answer (type-of exp2 tenv subst)
            (an-answer (ty2 subst)
              (an-answer
                (pair-type ty1 ty2)
                subst))))))
    (unpair-exp (var1 var2 exp body)
      (let ((ty1 (fresh-tvar-type))
            (ty2 (fresh-tvar-type)))
        (cases answer (type-of exp tenv subst)
          (an-answer (ty0 subst)
            (let ((subst (unifier ty0 (pair-type ty1 ty2) subst exp)))
              (type-of body 
                       (extend-tenv var1 (make-type-scheme '() ty1) 
                         (extend-tenv var2 (make-type-scheme '() ty2) tenv))
                       subst))))))
    (null-exp (exp1)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (let ((subst2 (unifier ty1 (list-type (fresh-tvar-type)) subst1 exp)))
            (an-answer (bool-type) subst2)))))
    (emptylist-exp ()
      (an-answer (list-type (fresh-tvar-type)) subst))
    (cons-exp (exp1 exp2)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (cases answer (type-of exp2 tenv subst1)
            (an-answer (ty2 subst2)
              (let ((subst3 (unifier (list-type ty1) ty2 subst2 exp)))
                (an-answer ty2 subst3)))))))
    (list-exp (exps)
      (if (null? exps)
          (an-answer (list-type (fresh-tvar-type)) subst)
          (cases answer* (type-of* exps tenv subst)
            (an-answer* (types subst1)
              (an-answer (list-type (car types)) (unify-all (cdr types) (car types) subst1 exp))))))
    (first-exp (exp1)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (let ((item-type (fresh-tvar-type)))
            (let ((subst2 (unifier ty1 (list-type item-type) subst1 exp)))
              (an-answer item-type subst2))))))
    (rest-exp (exp1)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst1)
          (let ((item-type (fresh-tvar-type)))
            (let ((subst2 (unifier ty1 (list-type item-type) subst1 exp)))
              (an-answer (list-type item-type) subst2))))))))
                

(define (type-of* exp* tenv subst)
  (define (loop exp* ty* subst)
    (if (null? exp*)
        (an-answer* (reverse ty*) subst)
        (cases answer (type-of (car exp*) tenv subst)
          (an-answer (t1 subst1)
            (loop (cdr exp*) (cons t1 ty*) subst1)))))
  (loop exp* '() subst))

(define (type-of-letrec p-result-types b-varss p-var-tyss p-bodies subst tenv-for-letrec-body)
  (if (null? p-bodies)
      subst
      (cases answer (type-of (car p-bodies) 
                             (extend-tenv* (car b-varss) (car p-var-tyss) tenv-for-letrec-body) 
                             subst)
        (an-answer (p-body-type subst1)
          (type-of-letrec
            (cdr p-result-types)
            (cdr b-varss)
            (cdr p-var-tyss)
            (cdr p-bodies)
            (unifier p-body-type (car p-result-types) subst1 (car p-bodies)) 
            tenv-for-letrec-body)))))

      

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
    (proc-type (arg-types res-type)
      (append (map type-to-external-form arg-types)
              (list '-> (type-to-external-form res-type))))
    (pair-type (ty1 ty2)
      (list (type-to-external-form ty1) 
            '* 
            (type-to-external-form ty2)))
    (list-type (ty)
      (list 'list-of (type-to-external-form ty)))
    (tvar-type (sn)
      (string->symbol      
        (string-append
          "ty"
          (number->string sn))))))


(define (free-type-vars ty tenv)
  (cases type ty
    (tvar-type (sn)
      (if (appears-in-tenv? ty tenv)
          '()
          (list ty)))
    (int-type () '())
    (bool-type () '())
    (pair-type (t1 t2)
      (set-union (free-type-vars t1 tenv)
                 (free-type-vars t2 tenv)))
    (list-type (t1)
      (free-type-vars t1 tenv))
    (proc-type (tas tr)
      (reduce set-union
              (free-type-vars tr tenv)
              (map (lambda (t) (free-type-vars t tenv)) tas)))))

(define (appears-in-tenv? tv tenv)
  (cases tenvironment tenv
    (empty-tenv () 
      #f)
    (extend-tenv (var tsm parent) 
      (if (appears-in-type? tv (type-scheme->type tsm)) 
          #t
          (appears-in-tenv? tv parent)))))

(define (appears-in-type? tv ty)
  (cases type ty
    (tvar-type (sn)
      (equal? tv ty))
    (int-type () #f)
    (bool-type () #f)
    (pair-type (t1 t2)
      (or (appears-in-type? tv t1)
          (appears-in-type? tv t2)))
    (list-type (ts)
      (reduce (lambda (a b) (or a b)) '()
        (map (lambda (t) (appears-in-type? tv t)) ts)))
    (proc-type (tas tr)
      (reduce (lambda (a b) (or a b))
              (appears-in-type? tv tr)
              (map (lambda (t) (appears-in-type? tv t)) tas)))))


(define (set-union set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        (else
          (set-union (set-add set1 (car set2))
                     (cdr set2)))))

(define (set-add set item)
  (cond ((null? set)
         (list item))
        ((equal? (car set) item)
         set)
        (else
         (cons (car set)
               (set-add (cdr set) item)))))
           
  

(define-datatype type-scheme type-scheme?
  (a-scheme (tvars (list-of tvar-type?))
            (ty type?)))

(define (make-type-scheme ty tenv)
  (a-scheme (free-type-vars ty tenv)
            ty))

(define (apply-type-scheme tsm)
  (cases type-scheme tsm
    (a-scheme (tvars ty)
      (reduce (lambda (t tv) 
                (apply-one-subst t tv (fresh-tvar-type)))
              ty
              tvars))))

(define (type-scheme->type tsm)
  (cases type-scheme tsm
    (a-scheme (tvars ty)
      ty)))

(define (reduce f init seq)
  (if (null? seq)
      init
      (reduce f (f init (car seq)) (cdr seq))))
              

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var symbol?) (tsm type-scheme?) (env tenvironment?)))

(define (polymorphic-extend-tenv* vars types env)
  (if (null? vars)
      env
      (polymorphic-extend-tenv* (cdr vars) (cdr types)
        (extend-tenv (car vars) (make-type-scheme (car types) env) env))))

(define (extend-tenv* vars types env)
  (if (null? vars)
      env
      (extend-tenv* (cdr vars) (cdr types)
        (extend-tenv (car vars) (a-scheme '() (car types)) env))))

(define (apply-tenv env search-var)
  (cases tenvironment env
    (empty-tenv () 
      (report-no-binding-found search-var))
    (extend-tenv (var ty parent) 
      (if (eqv? var search-var) 
        ty
        (apply-tenv parent search-var)))))


(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))



(define (otype->type otype)
  (cases optional-type otype
    (no-type () (fresh-tvar-type))
    (a-list-type () (list-type (fresh-tvar-type)))
    (a-type (ty) ty)))

(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))


(define (substitution? obj)
  (or (pair? obj) (null? obj)))

(define (apply-one-subst ty0 tvar ty1)
  (cases type ty0
    (int-type () (int-type))
    (bool-type () (bool-type))
    (proc-type (arg-types res-type)
      (proc-type
        (map (lambda (t) (apply-one-subst t tvar ty1)) arg-types)
        (apply-one-subst res-type tvar ty1)))
    (pair-type (a-type b-type)
      (pair-type
        (apply-one-subst a-type tvar ty1)
        (apply-one-subst b-type tvar ty1)))
    (list-type (ty)
      (list-type
        (apply-one-subst ty tvar ty1)))
    (tvar-type (sn)
      (if (equal? ty0 tvar) ty1 ty0))))

(define (apply-subst-to-type ty subst)
  (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t* t2)        
        (proc-type           
           (map (lambda (t) (apply-subst-to-type t subst)) t*)
           (apply-subst-to-type t2 subst)))
      (pair-type (t1 t2)
        (pair-type
           (apply-subst-to-type t1 subst)
           (apply-subst-to-type t2 subst)))
      (list-type (ty)
        (list-type
          (apply-subst-to-type ty subst)))
      (tvar-type (sn)
        (let ((tmp (assoc ty subst)))
          (if tmp (cdr tmp) ty)))))  

(define (empty-subst) '())

(define (extend-subst subst tvar ty)
  (cons (cons tvar ty)
        (map (lambda (p)
               (let ((oldlhs (car p))
                     (oldrhs (cdr p)))
                 (cons oldlhs (apply-one-subst oldrhs tvar ty))))
             subst)))

(define (unifier ty1 ty2 subst exp)
  (let ((ty1 (apply-subst-to-type ty1 subst))
        (ty2 (apply-subst-to-type ty2 subst)))
    (cond
      ((equal? ty1 ty2) subst)
      ((tvar-type? ty1)
       (if (no-occurrence? ty1 ty2)
           (extend-subst subst ty1 ty2)
           (report-no-occurrence-violation ty1 ty2 exp)))
      ((tvar-type? ty2)
       (if (no-occurrence? ty2 ty1)
           (extend-subst subst ty2 ty1)
           (report-no-occurrence-violation ty2 ty1 exp)))
      ((and (proc-type? ty1) (proc-type? ty2))
       (let ((subst (unify* (proc-type->arg-types ty1)
                            (proc-type->arg-types ty2)
                            subst exp)))
         (let ((subst (unifier (proc-type->res-type ty1)
                               (proc-type->res-type ty2)
                               subst exp)))
           subst)))
      ((and (list-type? ty1) (list-type? ty2))
       (unifier (list-type->item-type ty1)
                (list-type->item-type ty2)
                subst exp))
      (else (report-unification-failure ty1 ty2 exp)))))

(define (unify* t1* t2* subst exp)
  (if (null? t1*)
      subst
      (unify* (cdr t1*) (cdr t2*)
        (unifier (car t1*) (car t2*) subst exp)
        exp)))

(define (unify-all t* t1 subst exp)
  (if (null? t*)
      subst
      (unify-all (cdr t*) t1
        (unifier (car t*) t1 subst exp)
        exp)))

(define (tvar-type? ty1)
  (cases type ty1
    (tvar-type (sn) #t)
    (else #f)))

(define (proc-type? ty1)
  (cases type ty1
    (proc-type (a r) #t)
    (else #f)))

(define (list-type? ty1)
  (cases type ty1
    (list-type (t) #t)
    (else #f)))

(define (proc-type->arg-types ty1)
  (cases type ty1
    (proc-type (a r) a)
    (else 'not-a-proc-type)))

(define (proc-type->res-type ty1)
  (cases type ty1
    (proc-type (a r) r)
    (else 'not-a-proc-type)))  

(define (list-type->item-type ty1)
  (cases type ty1
    (list-type (t) t)
    (else 'not-a-list-type)))  

(define (no-occurrence? tvar ty)
  (cases type ty
    (int-type () #t)
    (bool-type () #t)
    (proc-type (arg-types res-type)
      (and (no-occurrence*? tvar arg-types)
           (no-occurrence? tvar res-type)))
    (pair-type (a-type b-type)
      (and (no-occurrence? tvar a-type)
           (no-occurrence? tvar b-type)))
    (list-type (t)
      (no-occurrence? tvar t))
    (tvar-type (sn)
      (not (equal? tvar ty)))))

(define (no-occurrence*? tvar ty*)
  (if (null? ty*)
      #t
      (and (no-occurrence? tvar (car ty*))
           (no-occurrence*? tvar (cdr ty*)))))

(define (report-unification-failure ty1 ty2 exp)
  (eopl:error 'unifier "Cannot unify ~s and ~s while inferring ~s" ty1 ty2 exp))

(define (report-no-occurrence-violation ty1 ty2 exp)
  (eopl:error 'unifier "~s occurs in ~s while inferring ~s" ty1 ty2 exp))


(define (equal-up-to-gensyms? sexp1 sexp2)
  (equal?
    (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
    (apply-subst-to-sexp (canonical-subst sexp2) sexp2)))

(define (canonical-subst sexp)
  (let loop ((sexp sexp) (table '()))
    (cond ((null? sexp) table)
          ((tvar-type-sym? sexp)
           (cond ((assq sexp table) table)
                 (else (cons (cons sexp (ctr->ty (length table)))
                             table))))
          ((pair? sexp)
           (loop (cdr sexp)
             (loop (car sexp) table)))
          (else table))))

(define (tvar-type-sym? sym)
  (and (symbol? sym)
       (char-numeric? (car (reverse (symbol->list sym))))))

(define (symbol->list x)
  (string->list (symbol->string x)))

(define (apply-subst-to-sexp subst sexp)
  (cond ((null? sexp) sexp)
        ((tvar-type-sym? sexp)
         (cdr (assq sexp subst)))
        ((pair? sexp)
         (cons (apply-subst-to-sexp subst (car sexp))
               (apply-subst-to-sexp subst (cdr sexp))))
        (else sexp)))

(define (ctr->ty n)
  (string->symbol
    (string-append "tvar" (number->string n))))


(define (assert-eval src expected)
  (let ((ty1 (type-to-external-form (check src)))
        (ty2 expected))
    (if (equal-up-to-gensyms? ty1 ty2)
        (display ".")
        (eopl:error 'assert "~s != ~s" ty1 ty2))))


(assert-eval 
  "42" 
  'int)

(assert-eval
  "-(8,5)"
  'int)

(assert-eval
  "zero? (0)"
  'bool)

(assert-eval
  "zero? (5)"
  'bool)

(assert-eval
  "if zero? (0) then 1 else 2"
  'int)

(assert-eval
  "let x = 123 in x"
  'int)

(assert-eval
  "proc (x:?) x"
  '(t1 -> t1))

(assert-eval
  "let x = 123 in proc (x:?) x"
  '(t1 -> t1))

(assert-eval
  "letrec ? double(x : ?) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in double"
  '(int -> int))

(assert-eval
  "proc (x : ?) newpair(x, x)"
  '(t1 -> (t1 * t1)))

(assert-eval
  "proc () 0"
  '(-> int))

(assert-eval
  "proc (x:int y:? z:?) y"
  '(int t1 t2 -> t1))

(assert-eval
  "let x = 1 y = 2 in newpair(x,y)"
  '(int * int))

(assert-eval
  "letrec 
     ? true() = zero?(0)
     ? false() = zero?(1)
     ? even(x:?) = if zero?(x) then (true) else (odd -(x,1))
     ? odd(x:?) = if zero?(x) then (false) else (even -(x,1))
   in
     newpair(even, odd)"
  '((int -> bool) * (int -> bool)))

(assert-eval
  "emptylist"
  '(list-of t1))

(assert-eval
  "list()"
  '(list-of t1))

(assert-eval
  "list(1)"
  '(list-of int))

(assert-eval
  "list(1,2,3)"
  '(list-of int))

(assert-eval
  "null?(emptylist)"
  'bool)

(assert-eval
  "null?(list(1,2))"
  'bool)

(assert-eval
  "cons(0,emptylist)"
  '(list-of int))

(assert-eval
  "proc (x:?) list(x,x)"
  '(t1 -> (list-of t1)))
  
(assert-eval
  "first(list(1))"
  'int)

(assert-eval
  "proc (x:[?]) first(x)"
  '((list-of t1) -> t1))

(assert-eval
  "proc (x:? y:?) cons(rest(x), rest(y))"
  '((list-of t1) (list-of (list-of t1)) -> (list-of (list-of t1))))

(assert-eval
  "let double = proc (x:?) -(x,-(0,x))
   in let id = proc (x:?) x
   in ((id double) (id 123))"
  'int)

(assert-eval
  "let f = proc (x:?) x
   in if (f zero?(0)) then (f 11) else (f 22)"   
   'int)

(assert-eval
  "letrec 
     ? map (f : ? x : ?) =
       if null?(x)
       then emptylist
       else cons((f first(x)), (map f rest(x)))
   in newpair((map proc (n:?) zero?(n) list(1,2,3)),
              (map proc (n:?) -(n,n) list(1,2,3)))"
  '((list-of bool) * (list-of int)))

(newline)
(display "OK")
(newline)
