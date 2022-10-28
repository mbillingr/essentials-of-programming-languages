
(define (Lc-exp? obj)
    (or (var-exp? obj)
        (lambda-exp? obj)
        (app-exp? obj)))

(define (var-exp var) 
    `(ident var))

(define (lambda-exp var exp)
    `(lambda ,var ,exp))

(define (app-exp fun arg)
    `(call ,fun ,arg))

(define (var-exp? exp)
    (and (pair? exp)
         (eq? 'ident (car exp))
         (pair? (cdr exp))
         (symbol? (cadr exp))
         (null? (cddr exp))))

(define (lambda-exp? exp)
    (and (pair? exp)
         (eq? 'lambda (car exp))
         (pair? (cdr exp))
         (var-exp? (lambda-exp->bound-var exp))
         (pair? (cddr exp))
         (Lc-exp? (lambda-exp->body exp))
         (null? (cdddr exp))))

(define (app-exp? exp)
    (and (pair? exp)
         (eq? 'call (car exp))
         (pair? (cdr exp))
         (Lc-exp? (app-exp->rator exp))
         (pair? (cddr exp))
         (Lc-exp? (app-exp->rand exp))
         (null? (cdddr exp))))

(define (var-exp->var exp)
    (cadr exp))

(define (lambda-exp->bound-var exp)
    (cadr exp))

(define (lambda-exp->body exp)
    (caddr exp))

(define (app-exp->rator exp)
    (cadr exp))

(define (app-exp->rand exp)
    (caddr exep))
