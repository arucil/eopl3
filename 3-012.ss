#lang eopl

;;; 3.12

(require "env.ss")
(require "racket-lib.ss")

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
     ("+" "(" expression "," expression ")")
     add-exp)

    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)

    (expression
     ("/" "(" expression "," expression ")")
     div-exp)

    (expression
     ("minus" "(" expression ")")
     minus-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("equal?" "(" expression "," expression ")")
     equal?-exp)

    (expression
     ("greater?" "(" expression "," expression ")")
     greater?-exp)

    (expression
     ("less?" "(" expression "," expression ")")
     less?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("emptylist")
     emptylist-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    (expression
     ("cond" (arbno expression "==>" expression) "end")
     cond-exp)
    
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
  (cons-val
   (car expval?)
   (cdr expval?))
  (null-val))

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

(define (expval->cons val)
  (cases expval val
    [cons-val (car cdr) (cons car cdr)]
    [else
     (eopl:error 'expval->list "expval ~A is not list" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (init-env)
  (extend-env 'i (num-val 1)
    (extend-env 'v (num-val 5)
      (extend-env 'x (num-val 10)
        (empty-env)))))

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
      (value-of exp (init-env))]))



(define (value-of-binary build-val op exp1 exp2 env)
  (build-val (op
            (expval->num (value-of exp1 env))
            (expval->num (value-of exp2 env)))))

(define (value-of-binary-num op exp1 exp2 env)
  (value-of-binary num-val op exp1 exp2 env))

(define (value-of-binary-bool op exp1 exp2 env)
  (value-of-binary bool-val op exp1 exp2 env))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
      (value-of-binary-num - exp1 exp2 env)]
    [add-exp (exp1 exp2)
      (value-of-binary-num + exp1 exp2 env)]
    [mult-exp (exp1 exp2)
      (value-of-binary-num * exp1 exp2 env)]
    [div-exp (exp1 exp2)
      (value-of-binary-num quotient exp1 exp2 env)]
    [equal?-exp (exp1 exp2)
      (value-of-binary-bool equal? exp1 exp2 env)]
    [greater?-exp (exp1 exp2)
      (value-of-binary-bool > exp1 exp2 env)]
    [less?-exp (exp1 exp2)
      (value-of-binary-bool < exp1 exp2 env)]
    [var-exp (var)
      (apply-env env var)]
    [minus-exp (exp)
      (num-val (-
                (expval->num
                 (value-of exp env))))]
    [zero?-exp (exp)
      (bool-val (zero?
                 (expval->num
                  (value-of exp env))))]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (var exp body)
      (value-of body
        (extend-env var (value-of exp env) env))]

    [cons-exp (exp1 exp2)
      (cons-val (value-of exp1 env)
                (value-of exp2 env))]
    [car-exp (exp)
      (car (expval->cons
            (value-of exp env)))]
    [cdr-exp (exp)
      (cdr (expval->cons
            (value-of exp env)))]
    [null?-exp (exp)
      (bool-val (expval-null?
                 (value-of exp env)))]
    [emptylist-exp ()
      (null-val)]

    [list-exp (list)
      (letrec ([rec (lambda (ls env)
                      (if (null? ls)
                          (null-val)
                          (cons-val (value-of (car ls) env)
                                    (rec (cdr ls) env))))])
        (rec list env))]
    [cond-exp (exp-list1 exp-list2)
      (letrec ([rec (lambda (ls1 ls2 env)
                      (cond
                        [(null? ls1)
                         (eopl:error 'value-of "cond expression failed")]
                        [(expval->bool (value-of (car ls1) env))
                         (value-of (car ls2) env)]
                        [else
                         (rec (cdr ls1) (cdr ls2) env)]))])
        (rec exp-list1 exp-list2 env))]))