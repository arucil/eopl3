#lang eopl

;;; 3.28  2)

;; procedural representation

(require "env.ss")
(require "racket-lib.ss")

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "*" "/" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)
    
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
   (bool boolean?))
  (proc-val
   (proc procedure?)))

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

(define (expval->proc val)
  (cases expval val
    [proc-val (proc) proc]
    [else
     (eopl:error 'expval->proc "expval ~A is not proc" val)]))

(define (procedure var body)
  (lambda (val env)
    (value-of body
              (extend-env var val env))))

(define (apply-procedure p val env)
  (p val env))

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
      (value-of exp (empty-env))]))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
      (num-val (-
                (expval->num (value-of exp1 env))
                (expval->num (value-of exp2 env))))]
    [var-exp (var)
      (apply-env env var)]
    [zero?-exp (exp)
      (bool-val (zero?
                 (expval->num
                  (value-of exp env))))]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (var-list exp-list body)
      (letrec ([rec (lambda (var-list exp-list e)
                      (if (null? var-list)
                          e
                          (rec (cdr var-list)
                            (cdr exp-list)
                            (extend-env (car var-list)
                                        (value-of (car exp-list) env)
                                        e))))])
        (value-of body (rec var-list exp-list env)))]

    ;;; procedures
    [proc-exp (var exp)
              (proc-val (procedure var exp))]

    [call-exp (exp1 exp2)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of exp2 env)
                               env)]))