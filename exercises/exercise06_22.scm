#lang eopl

; CPS-OUT lang (interpreter)

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-cps-in-grammar
  '((in-program (in-exp) a-in-program)

    (in-exp (number) const-exp)

    (in-exp
      ("-" "(" in-exp "," in-exp ")")
      diff-exp)

    (in-exp
      ("+" "(" (separated-list in-exp ",") ")")
      sum-exp)
    
    (in-exp
      ("zero?" "(" in-exp ")")
      zero?-exp)

    (in-exp
      ("if" in-exp "then" in-exp "else" in-exp)
      if-exp)

    (in-exp (identifier) var-exp)

    (in-exp
      ("let" identifier "=" in-exp "in" in-exp)
      let-exp)

    (in-exp
      ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" in-exp) "in" in-exp)
      letrec-exp)

    (in-exp
      ("proc" "(" (arbno identifier) ")" in-exp)
      proc-exp)

    (in-exp
      ("(" in-exp (arbno in-exp) ")")
      call-exp)))
      
(define the-cps-out-grammar
  '((program (tfexp) a-cps-program)

    (simple-exp 
      (number) 
      cps-const-exp)

    (simple-exp
      (identifier) 
      cps-var-exp)

    (simple-exp
      ("-" "(" simple-exp "," simple-exp ")")
      cps-diff-exp)

    (simple-exp
      ("+" "(" (separated-list simple-exp ",") ")")
      cps-sum-exp)
    
    (simple-exp
      ("zero?" "(" simple-exp ")")
      cps-zero?-exp)

    (simple-exp
      ("proc" "(" (arbno identifier) ")" tfexp)
      cps-proc-exp)

    (tfexp
      (simple-exp)
      simple-exp->exp)

    (tfexp
      ("let" identifier "=" simple-exp "in" tfexp)
      cps-let-exp)

    (tfexp
      ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp) "in" tfexp)
      cps-letrec-exp)

    (tfexp
      ("if" simple-exp "then" tfexp "else" tfexp)
      cps-if-exp)

    (tfexp
      ("(" simple-exp (arbno simple-exp) ")")
      cps-call-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-cps-in-grammar)
(sllgen:make-define-datatypes the-lexical-spec the-cps-out-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-cps-in-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-cps-in-grammar))


(define (cps-of-program in-prog)
  (cases in-program in-prog
    (a-in-program (in-exp)
      (a-cps-program 
        (cps-of-exps (list in-exp) 
          (lambda (new-args)
            (simple-exp->exp (car new-args))))))))

(define (cps-of-exp exp k-exp)
  (cases in-exp exp
    (const-exp (num)
      (make-send-to-cont k-exp (cps-const-exp num)))
    (var-exp (var)
      (make-send-to-cont k-exp (cps-var-exp var)))
    (proc-exp (vars body)
      (make-send-to-cont k-exp
        (cps-proc-exp (append vars '(k%00))
          (cps-of-exp body (cps-var-exp 'k%00)))))
    (zero?-exp (exp1)
      (cps-of-zero?-exp exp1 k-exp))
    (diff-exp (exp1 exp2)
      (cps-of-diff-exp exp1 exp2 k-exp))
    (sum-exp (exps)
      (cps-of-sum-exp exps k-exp))
    (if-exp (exp1 exp2 exp3)
      (cps-of-if-exp exp1 exp2 exp3 k-exp))
    (let-exp (var exp1 body)
      (cps-of-let-exp var exp1 body k-exp))
    (letrec-exp (p-names b-varss p-bodies letrec-body)
      (cps-of-letrec-exp p-names b-varss p-bodies letrec-body k-exp))
    (call-exp (rator rands)
      (cps-of-call-exp rator rands k-exp))))

(define (cps-of-simple-exp exp)
  (cases in-exp exp
    (const-exp (num) (cps-const-exp num))
    (var-exp (var) (cps-var-exp var))
    (diff-exp (exp1 exp2) 
      (cps-diff-exp (cps-of-simple-exp exp1) (cps-of-simple-exp exp2)))
    (zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1)))
    (proc-exp (ids body)
      (cps-proc-exp (append ids '(k%00))
        (cps-of-exp body (cps-var-exp 'k%00))))
    (sum-exp (exps)
      (cps-sum-exp (map cps-of-simple-exp exps)))
    (else
       (report-invalid-exp-to-cps-of-simple-exp exp))))

(define (report-invalid-exp-to-cps-of-simple-exp exp)
  (eopl:error 'cps-of-simple-exp "Not a simple exp ~s" exp))

(define (cps-of-zero?-exp exp1 k-exp)
  (cps-of-exps (list exp1)
    (lambda (simples)
      (make-send-to-cont
        k-exp
        (cps-zero?-exp (car simples))))))

(define (cps-of-diff-exp exp1 exp2 k-exp)
  (cps-of-exps (list exp1 exp2)
    (lambda (simples)
      (make-send-to-cont
        k-exp
        (cps-diff-exp (car simples) (cadr simples))))))

(define (cps-of-if-exp exp1 exp2 exp3 k-exp)
  (cps-of-exps (list exp1)
    (lambda (simples)
      (cps-if-exp (car simples)
        (cps-of-exp exp2 k-exp)
        (cps-of-exp exp3 k-exp)))))

(define (cps-of-let-exp id rhs body k-exp)
  (cps-of-exps (list rhs)
    (lambda (simples)
      (cps-let-exp id
         (car simples)
         (cps-of-exp body k-exp)))))

(define (cps-of-letrec-exp p-names b-varss p-bodies letrec-body k-exp)
  (cps-letrec-exp
    p-names
    (map (lambda (b-vars) (append b-vars '(k%00))) 
         b-varss)
    (map (lambda (p-body)
           (cps-of-exp p-body (cps-var-exp 'k%00)))
         p-bodies)
    (cps-of-exp letrec-body k-exp)))

(define (cps-of-sum-exp exps k-exp)
  (cps-of-exps exps
    (lambda (simples)
      (make-send-to-cont
        k-exp
        (cps-sum-exp simples)))))

(define (cps-of-call-exp rator rands k-exp)
  (cps-of-exps (cons rator rands)
    (lambda (simples)
      (cps-call-exp 
        (car simples)
        (append (cdr simples) (list k-exp))))))

(define (cps-of-exps exps builder)
  (let cps-of-rest ((exps exps))
    (let ((pos (list-index
                  (lambda (exp) (not (inp-exp-simple? exp)))
                  exps)))
      (if (not pos)
          (builder (map cps-of-simple-exp exps))
          (let ((var (fresh-identifier 'var)))
            (cps-of-exp
               (list-ref exps pos)
               (cps-proc-exp (list var)
                 (cps-of-rest
                    (list-set exps pos (var-exp var))))))))))

(define (inp-exp-simple? exp)
  (cases in-exp exp
    (const-exp (num) #t)
    (var-exp (var) #t)
    (diff-exp (exp1 exp2) (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
    (zero?-exp (exp1) (inp-exp-simple? exp1))
    (proc-exp (ids exp) #t)
    (sum-exp (exps) (every? inp-exp-simple? exps))
    (else #f)))


(define (make-send-to-cont k-exp sexp)
  (cases simple-exp k-exp
    (cps-proc-exp (vars body) 
      (cps-let-exp (car vars) sexp body))
    (else (cps-call-exp k-exp (list sexp)))))

(define (list-index pred seq)
  (define (list-index/k pred seq pos)
    (cond ((null? seq)
           #f)
          ((pred (car seq))
           pos)
          (else
            (list-index/k pred (cdr seq) (+ 1 pos)))))
  (list-index/k pred seq 0))

(define (list-set seq pos val)
  (if (eqv? pos 0)
      (cons val (cdr seq))
      (cons (car seq) (list-set (cdr seq) (- pos 1) val))))

(define (every? pred seq)
  (cond ((null? seq)
         #t)
        ((pred (car seq))
         (every? pred (cdr seq)))
        (else #f)))

(define fresh-identifier
  (let ((sn 0))
    (lambda (name)
      (set! sn (+ 1 sn))
      (string->symbol
        (string-append
          (symbol->string name)
          "%"
          (number->string sn))))))


(define (run source)
  (value-of-program 
    (cps-of-program
      (scan&parse source))))

(define (value-of-program pgm)
  (cases program pgm
    (a-cps-program (exp1)
      (value-of/k exp1 (empty-env) (end-cont)))))

(define (value-of/k exp env cont)
  (cases tfexp exp
    (simple-exp->exp (simple) 
      (apply-cont cont
        (value-of-simple-exp simple env)))
    (cps-let-exp (var rhs body)
      (let ((val (value-of-simple-exp rhs env)))
        (value-of/k body
          (extend-env* (list var) (list val) env)
          cont)))
    (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
      (value-of/k letrec-body 
        (extend-env-rec** p-names b-varss p-bodies env)
        cont))
    (cps-if-exp (simple1 body1 body2)
      (if (expval->bool (value-of-simple-exp simple1 env))
          (value-of/k body1 env cont)
          (value-of/k body2 env cont)))
    (cps-call-exp (rator rands)
      (let ((rator-proc (expval->proc (value-of-simple-exp rator env)))
            (rand-vals (map (lambda (simple) (value-of-simple-exp simple env)) rands)))
        (apply-procedure/k rator-proc rand-vals cont)))))

(define (value-of-simple-exp simple env)
  (cases simple-exp simple
    (cps-const-exp (num)
      (num-val num))
    (cps-var-exp (var)
      (apply-env env var))
    (cps-diff-exp (simple1 simple2)
      (num-val (- (expval->num (value-of-simple-exp simple1 env))
                  (expval->num (value-of-simple-exp simple2 env))))) 
    (cps-sum-exp (simples)
      (num-val (apply + (map (lambda (x) (expval->num (value-of-simple-exp x env))) simples))))
    (cps-zero?-exp (simple1)
      (bool-val (zero? (expval->num (value-of-simple-exp simple1 env)))))
    (cps-proc-exp (vars body)
      (proc-val (procedure vars body env)))))

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


(define-datatype proc proc?
  (procedure
    (vars (list-of symbol?))
    (body tfexp?)
    (env environment?)))    

(define (apply-procedure/k proc1 args cont)
  (cases proc proc1
    (procedure (vars body saved-env)
      (value-of/k body
        (extend-env* vars args saved-env)
        cont))))


(define-datatype environment environment?
  (empty-env)
  (extend-env* 
    (var (list-of symbol?)) 
    (val (list-of expval?)) 
    (env environment?))
  (extend-env-rec** 
    (p-names (list-of symbol?)) 
    (b-varss (list-of (list-of symbol?))) 
    (p-bodies (list-of tfexp?)) 
    (env environment?)))

(define (apply-env env search-var)
  (cases environment env
    (empty-env () 
      (report-no-binding-found search-var))
    (extend-env* (vars vals saved-env) 
      (lookup search-var vars vals saved-env))
    (extend-env-rec** (p-names b-varss p-bodies saved-env)
      (lookup-rec search-var p-names b-varss p-bodies env saved-env))))

(define (lookup search-var vars vals next-env)
  (cond ((null? vars)
         (apply-env next-env search-var))
        ((eqv? (car vars) search-var)
         (car vals))
        (else
          (lookup search-var (cdr vars) (cdr vals) next-env))))

(define (lookup-rec search-var p-names b-varss p-bodies current-env next-env)
  (cond ((null? p-names)
         (apply-env next-env search-var))
        ((eqv? (car p-names) search-var)
         (proc-val
           (procedure
             (car b-varss)
             (car p-bodies)
             current-env)))
        (else
          (lookup-rec search-var (cdr p-names) (cdr b-varss) (cdr p-bodies) current-env next-env))))

(define (report-no-binding-found var)
  (eopl:error 'apply-env "No binding for ~s" var))


(define-datatype continuation continuation?
  (end-cont))

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
        (begin ;(println "End of computation.")
               val)))))

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
  "letrec 
     finish(x) = x
     double(x k) = 
       if zero?(x) 
       then (k x) 
       else letrec double1(y) = (k +(y, 2))
            in (double -(x,1) double1)
   in (double 6 finish)"
  (num-val 12))

(eopl:pretty-print (cps-of-program (scan&parse "if zero? (0) then 1 else 2")))

(newline)
(display "OK")
