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

    (optional-type
      ()
      no-type)

    (optional-type
      (":" type)
      a-type)

    (optional-res-type
      ()
      no-res-type)

    (optional-res-type
      (type)
      a-res-type)

    (optionally-typed-identifier
      (identifier optional-type)
      typed-identifier)

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
      ("letrec" optional-res-type identifier "(" identifier optional-type ")" "=" expression "in" expression)
      letrec-exp)

    (expression
      ("proc" "(" identifier optional-type ")" expression)
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


(display
  (scan&parse
    "letrec double(x) = if zero?(x) then 0 else -((double -(x,1)), -2)
     in (double 6)"))
(newline)

(display
  (scan&parse
    "proc (x) x"))
(newline)