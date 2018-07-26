#lang eopl

;;; 3.22

;; modify diff-exp to:
;;  (- expression expression)
;; there must be no spaces between '(' and '-'.

(require "env.ss")
(require "racket-lib.ss")

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    ;; (comment ("%" (arbno (not #\newline))) skip)
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
     ("(-" expression expression ")")
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
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    (expression
     ("letproc" identifier "(" (separated-list identifier ",") ")" expression "in" expression)
     letproc-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

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

(define (apply-procedure p ls)
  (cases proc p
    [procedure (var-list body env)
               (letrec ([rec (lambda (var-list val-list e)
                               (if (null? var-list)
                                   (value-of body e)
                                   (rec (cdr var-list)
                                     (cdr val-list)
                                     (extend-env (car var-list)
                                                 (car val-list)
                                                 e))))])
                 (rec var-list ls env))]))

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
    [let-exp (var exp body)
             (value-of body (extend-env var
                                        (value-of exp env)
                                        env))]

    ;;; procedures
    [proc-exp (var-list exp)
              (proc-val (procedure var-list exp env))]

    [call-exp (exp1 exp-list)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exp-list))]

    ;; letproc
    [letproc-exp (var args body exp)
                 (value-of exp (extend-env var
                                           (proc-val (procedure args body env))
                                           env))]))