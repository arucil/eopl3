#lang eopl

;;; 3.6

(require "env.ss")

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    ;; (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    ;; (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("minus" "(" expression ")")
     minus-exp)
    
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
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?)))

(define (expval->num val)
  (cases expval val
    [num-val (num) num]
    [else
     (eopl:error 'expval-num "expval ~A is not num" val)]))

(define (expval->bool val)
  (cases expval val
    [bool-val (bool) bool]
    [else
     (eopl:error 'expval->bool "expval ~A is not bool" val)]))

(define (init-env)
  (extend-env 'i (num-val 1)
    (extend-env 'v (num-val 5)
      (extend-env 'x (num-val 10)
        (empty-env)))))

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
      (value-of exp (init-env))]))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num) (num-val num)]
    [diff-exp (exp1 exp2)
      (num-val (-
                (expval->num (value-of exp1 env))
                (expval->num (value-of exp2 env))))]
    [var-exp (var)
      (apply-env env var)]
    [minus-exp (exp) (num-val (- (expval->num (value-of exp env))))]
    [zero?-exp (exp) (bool-val (zero? (expval->num (value-of exp env))))]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (var exp body)
      (value-of body
        (extend-env var (value-of exp env) env))]))