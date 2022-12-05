#lang eopl

; INFERRED lang, with ...
;   - pairs

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

    (type
      ("pairof" type "*" type)
      pair-type)

    (type
      ("%tvar-type" number)
      tvar-type)

    (optional-type
      ("?")
      no-type)

    (optional-type
      (type)
      a-type)

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
      ("letrec" optional-type identifier "(" identifier ":" optional-type ")" "=" expression "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" identifier ":" optional-type ")" expression)
      proc-exp)

    (expression
      ("(" expression expression ")")
      call-exp)

    (expression
      ("newpair" "(" expression "," expression ")")
      pair-exp)

    (expression
      ("unpair" identifier identifier "=" expression "in" expression)
      unpair-exp)))


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
    (var-exp (var) (an-answer (apply-tenv tenv var) subst))
    (let-exp (var exp1 body)
      (cases answer (type-of exp1 tenv subst)
        (an-answer (ty1 subst)
          (type-of body
            (extend-tenv var ty1 tenv)
            subst))))
    (proc-exp (var otype body)
      (let ((var-type (otype->type otype)))
        (cases answer (type-of body
                               (extend-tenv var var-type tenv)
                               subst)
          (an-answer (body-type subst)
            (an-answer
              (proc-type var-type body-type)
              subst)))))
    (call-exp (rator rand)
      (let ((result-type (fresh-tvar-type)))
        (cases answer (type-of rator tenv subst)
          (an-answer (rator-type subst)
            (cases answer (type-of rand tenv subst)
              (an-answer (rand-type subst)
                (let ((subst (unifier rator-type
                                      (proc-type rand-type result-type)
                                      subst exp)))
                  (an-answer result-type subst))))))))
    (letrec-exp (p-result-otype p-name b-var b-var-otype p-body letrec-body)
      (let ((p-result-type (otype->type p-result-otype))
            (p-var-type (otype->type b-var-otype)))
        (let ((tenv-for-letrec-body
                (extend-tenv p-name
                  (proc-type p-var-type p-result-type)
                  tenv)))
          (cases answer (type-of p-body (extend-tenv b-var p-var-type tenv-for-letrec-body) subst)
            (an-answer (p-body-type subst)
              (let ((subst (unifier p-body-type p-result-type subst p-body)))
                (type-of letrec-body
                         tenv-for-letrec-body
                         subst)))))))
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
                       (extend-tenv var1 ty1 (extend-tenv var2 ty2 tenv)) 
                       subst))))))))

      

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
    (pair-type (ty1 ty2)
      (list (type-to-external-form ty1) 
            '* 
            (type-to-external-form ty2)))
    (tvar-type (sn)
      (string->symbol      
        (string-append
          "ty"
          (number->string sn))))))


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


(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))



(define (otype->type otype)
  (cases optional-type otype
    (no-type () (fresh-tvar-type))
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
    (proc-type (arg-type res-type)
      (proc-type
        (apply-one-subst arg-type tvar ty1)
        (apply-one-subst res-type tvar ty1)))
    (pair-type (a-type b-type)
      (pair-type
        (apply-one-subst a-type tvar ty1)
        (apply-one-subst b-type tvar ty1)))
    (tvar-type (sn)
      (if (equal? ty0 tvar) ty1 ty0))))

(define (apply-subst-to-type ty subst)
  (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
        (proc-type
           (apply-subst-to-type t1 subst)
           (apply-subst-to-type t2 subst)))
      (pair-type (t1 t2)
        (pair-type
           (apply-subst-to-type t1 subst)
           (apply-subst-to-type t2 subst)))
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
       (let ((subst (unifier (proc-type->arg-type ty1)
                             (proc-type->arg-type ty2)
                             subst exp)))
         (let ((subst (unifier (proc-type->res-type ty1)
                               (proc-type->res-type ty2)
                               subst exp)))
           subst)))
      (else (report-unification-failure ty1 ty2 exp)))))

(define (tvar-type? ty1)
  (cases type ty1
    (tvar-type (sn) #t)
    (else #f)))

(define (proc-type? ty1)
  (cases type ty1
    (proc-type (a b) #t)
    (else #f)))

(define (proc-type->arg-type ty1)
  (cases type ty1
    (proc-type (a b) a)
    (else 'not-a-proc-type)))

(define (proc-type->res-type ty1)
  (cases type ty1
    (proc-type (a b) b)
    (else 'not-a-proc-type)))  

(define (no-occurrence? tvar ty)
  (cases type ty
    (int-type () #t)
    (bool-type () #t)
    (proc-type (arg-type res-type)
      (and (no-occurrence? tvar arg-type)
           (no-occurrence? tvar res-type)))
    (pair-type (a-type b-type)
      (and (no-occurrence? tvar a-type)
           (no-occurrence? tvar b-type)))
    (tvar-type (sn)
      (not (equal? tvar ty)))))

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
        (ty2 (type-to-external-form expected)))
    (if (equal-up-to-gensyms? ty1 ty2)
        (display ".")
        (eopl:error 'assert "~s != ~s" ty1 ty2))))


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
  "let x = 123 in proc (x : ?) x"
  (proc-type (tvar-type 1) (tvar-type 1)))

(assert-eval
  "letrec ? double(x : ?) = if zero?(x) then 0 else -((double -(x,1)), -2)
   in double"
  (proc-type (int-type) (int-type)))

(assert-eval
  "proc (x : ?) newpair(x, x)"
  (proc-type (tvar-type 1) (pair-type (tvar-type 1) (tvar-type 1))))

(newline)
(display "OK")
(newline)