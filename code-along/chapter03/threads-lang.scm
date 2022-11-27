#lang eopl

; THREADS lang 

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
      ("begin" expression (arbno expression) "end")
      begin-exp)

    (expression
      ("set" identifier "=" expression)
      assign-exp)

    (expression
      ("spawn" "(" expression ")")
      spawn-exp)

    (expression
      ("mutex" "(" ")")
      mutex-exp)

    (expression
      ("wait" "(" expression ")")
      wait-exp)

    (expression
      ("signal" "(" expression ")")
      signal-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))
  
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
  
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


(define (run source)
  (value-of-program 1 (scan&parse source)))

(define (value-of-program timeslice pgm)
  (initialize-store!)
  (initialize-scheduler! timeslice)
  (cases program pgm
    (a-program (exp1)
      (value-of/k exp1 (init-env) (end-main-thread-cont)))))

(define (value-of/k exp env cont)
  (cases expression exp
    (const-exp (num) (apply-cont cont (num-val num)))
    (var-exp (var) (apply-cont cont (deref (apply-env env var))))
    (proc-exp (var body)
      (apply-cont cont
        (proc-val (procedure var body env))))
    (letrec-exp (proc-name* bound-var* proc-body* letrec-body)
      (value-of/k letrec-body 
                  (extend-env-rec proc-name* bound-var* proc-body* env)
                  cont))
    (zero?-exp (exp1)
      (value-of/k exp1 env (zero1-cont cont)))
    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
    (let-exp (var exp1 body)
      (value-of/k exp1 env (let-exp-cont var body env cont)))
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont)))
    (call-exp (rator rand)
      (value-of/k rator env (rator-cont rand env cont)))
    (begin-exp (first rest)
      (if (null? rest)
          (value-of/k first env cont)    
          (value-of/k 
            (call-exp
              (proc-exp
                (fresh-identifier 'dummy)
                (begin-exp (car rest) (cdr rest)))
              first)
            env
            cont)))
    (assign-exp (var exp1)
      (value-of/k exp1 env (set-rhs-cont var env cont)))
    (spawn-exp (exp1)
      (value-of/k exp1 env (spawn-cont cont)))
    (mutex-exp ()
      (apply-cont cont (mutex-val (new-mutex))))
    (wait-exp (exp1)
      (value-of/k exp1 env (wait-cont cont)))
    (signal-exp (exp1)
      (value-of/k exp1 env (signal-cont cont)))))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (ref-val (ref reference?))
  (mutex-val (mut mutex?)))

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

(define (expval->mutex val)    
  (cases expval val
    (mutex-val (ref) ref)
    (else (report-expval-extractor-error 'mutex val))))

(define (report-expval-extractor-error kind val)
  (eopl:error kind "expected ~s but got value ~s" kind val))


(define (proc? val)
  (procedure? val))

(define (procedure var body env)
  (lambda (val cont)
    (value-of/k body (extend-env var (newref val) env) cont)))

(define (apply-procedure/k proc1 val cont)
  (proc1 val cont))


(define-datatype mutex mutex?
  (a-mutex
    (ref-to-closed? reference?)
    (ref-to-wait-queue reference?)))

(define (new-mutex)
  (a-mutex (newref #f) (newref '())))


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


(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont 
    (cont continuation?))
  (let-exp-cont
    (var symbol?)
    (body expression?)
    (env environment?)
    (cont continuation?))
  (if-test-cont
    (exp2 expression?)
    (exp3 expression?)
    (env environment?)
    (cont continuation?))
  (diff1-cont 
    (exp2 expression?)
    (env environment?) 
    (cont continuation?))
  (diff2-cont 
    (val1 expval?)
    (cont continuation?))
  (rator-cont 
    (rand expression?)
    (env environment?)
    (cont continuation?))  
  (application-cont 
    (proc procedure?)
    (cont continuation?))
  (set-rhs-cont
    (var symbol?)
    (env environment?)
    (cont continuation?))
  (spawn-cont
    (cont continuation?))
  (end-main-thread-cont)
  (end-subthread-cont)
  (wait-cont
    (cont continuation?))
  (signal-cont
    (cont continuation?)))

(define apply-cont
  (lambda (cont val)
    (if (time-expired?)
        (begin
          (place-on-ready-queue!
            (lambda () (apply-cont cont val)))
          (run-next-thread))
        (begin
          (decrement-timer!)
          (cases continuation cont
            (end-cont ()
              (begin ;(println "End of computation.")
                     val))
            (zero1-cont (saved-cont)
              (apply-cont saved-cont
                (bool-val (zero? (expval->num val)))))
            (let-exp-cont (var body saved-env saved-cont)
              (value-of/k body
                (extend-env var (newref val) saved-env) saved-cont))
            (if-test-cont (exp2 exp3 saved-env saved-cont)
              (value-of/k (if (expval->bool val) exp2 exp3)
                          saved-env saved-cont))
            (diff1-cont (exp2 env saved-cont)
              (value-of/k exp2 env (diff2-cont val saved-cont)))
            (diff2-cont (val1 saved-cont)
              (apply-cont saved-cont
                (num-val (- (expval->num val1) (expval->num val)))))
            (rator-cont (rand saved-env saved-cont)
              (value-of/k rand saved-env 
                (application-cont (expval->proc val) saved-cont)))
            (application-cont (proc saved-cont)
              (apply-procedure/k proc val saved-cont))
            (set-rhs-cont (var env cont)
              (begin 
                ;(display "setting ") (display var) (display " = ") (display val) (newline)
                (setref!
                   (apply-env env var)
                   val)
                (apply-cont cont (num-val 27))))
            (spawn-cont (saved-cont)
              (let ((proc1 (expval->proc val)))
                (place-on-ready-queue!
                  (lambda ()
                    (apply-procedure/k proc1 (num-val 28) (end-subthread-cont))))
                (apply-cont saved-cont (num-val 73))))
            (end-main-thread-cont ()
              ;(display "end of main thread")(newline)
              (set-final-answer! val)
              (run-next-thread))
            (end-subthread-cont ()
              ;(display "end of sub thread")(newline)
              (run-next-thread))
            (wait-cont (saved-cont)
              (wait-for-mutex
                (expval->mutex val)
                (lambda () (apply-cont saved-cont (num-val 52)))))
            (signal-cont (saved-cont)
              (signal-mutex
                (expval->mutex val)
                (lambda () (apply-cont saved-cont (num-val 53))))))))))


(define (wait-for-mutex m th)
  (cases mutex m
    (a-mutex (ref-to-closed? ref-to-wait-queue)
      (cond
        ((deref ref-to-closed?)
         (setref! ref-to-wait-queue
            (enqueue (deref ref-to-wait-queue) th))
         (run-next-thread))
        (else
          (setref! ref-to-closed? #t)
          (th))))))

(define (signal-mutex m th)
  (cases mutex m
    (a-mutex (ref-to-closed? ref-to-wait-queue)
      (let ((closed? (deref ref-to-closed?))
            (wait-queue (deref ref-to-wait-queue)))
        (if closed?
            (if (empty? wait-queue)
                (setref! ref-to-closed? #f)
                (dequeue wait-queue
                  (lambda (first-waiting-th other-waiting-ths)                    
                    (place-on-ready-queue! first-waiting-th)
                    (setref! ref-to-wait-queue other-waiting-ths))))
            'ok)
        (th)))))

    
(define the-ready-queue 'uninitialized)
(define the-final-answer 'uninitialized)
(define the-max-time-slice 'uninitialized)
(define the-time-remaining 'uninitialized)

(define (initialize-scheduler! ticks)
  (set! the-ready-queue (empty-queue))
  (set! the-final-answer 'uninitialized)
  (set! the-max-time-slice ticks)
  (set! the-time-remaining the-max-time-slice))

(define (place-on-ready-queue! th)
  (set! the-ready-queue (enqueue the-ready-queue th)))

(define (run-next-thread)
  (if (empty? the-ready-queue)
      the-final-answer
      (dequeue the-ready-queue
        (lambda (first-ready-thread other-ready-threads)
          (set! the-ready-queue other-ready-threads)
          (set! the-time-remaining the-max-time-slice)
          (first-ready-thread)))))

(define (set-final-answer! val)
  (set! the-final-answer val))

(define (time-expired?)
  (zero? the-time-remaining))

(define (decrement-timer!)
  (set! the-time-remaining (- the-time-remaining 1)))


(define (empty-queue)
  '())

(define (empty? queue)
  (null? queue))

(define (enqueue queue item)
  (append queue (list item)))

(define (dequeue queue fun)
  (fun (car queue) (cdr queue)))


(define fresh-identifier
  (let ((sn 0))
    (lambda (name)
      (set! sn (+ 1 sn))
      (string->symbol
        (string-append
          (symbol->string name)
          "%"
          (number->string sn))))))


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
  "let x = 123 in begin set x = 42 x end"
  (num-val 42))


(newline)
(display "OK")
(newline)


; see how the result changes when commenting out the `wait(mut)` line...
(newline)
(display (run "let x = 0
               in let mut = mutex()
               in let inc_x = proc (id) proc (dummy) 
                              begin
                                wait(mut)
                                let tmp = -(x,-1)
                                in begin
                                   1 2 3 4
                                   set x = tmp 
                                end
                                signal(mut)
                              end
               in begin
                  spawn((inc_x 100))
                  spawn((inc_x 200))
                  spawn((inc_x 300))
                  % waste a few cycles to give the threads time to finish
                  1 2 3 4 5 6 7 8 9 
                  1 2 3 4 5 6 7 8 9 
                  1 2 3 4 5 6 7 8 9 
                  x
               end"))
(newline)
