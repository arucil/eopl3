#lang eopl

;;; 3.36

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
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val (lambda (x)
          (or (vector? x)
              (expval? x))))
   (env environment?)))

(define (extend-env-rec p-name-list b-vars-list body-list env)
  (letrec ([extend (lambda (p-name-list e)
                     (if (null? p-name-list)
                         e
                         (extend (cdr p-name-list)
                                 (extend-env (car p-name-list)
                                             (make-vector 1 '())
                                             e))))]
           [build (lambda (p-name-list b-vars-list body-list e)
                    (cond
                      [(null? p-name-list)
                       e]
                      [else
                       (vector-set! (apply-env e (car p-name-list))
                                    0
                                    (proc-val (procedure (car b-vars-list)
                                                         (car body-list)
                                                         e)))
                       (build (cdr p-name-list)
                              (cdr b-vars-list)
                              (cdr body-list)
                              e)]))])
    (build p-name-list b-vars-list body-list (extend p-name-list env))))
                                             

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var val env)
                (if (eqv? var svar)
                    (if (vector? val)
                        (let ([v (vector-ref val 0)])
                          (if (null? v)
                              val
                              v))
                        val)
                    (apply-env env svar))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (var (list-of identifier?))
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

(define (apply-procedure p vals)
  (cases proc p
    [procedure (vars body env)
               (let rec ([vars vars] [vals vals] [env env])
                 (if (null? vars)
                    (value-of body env)
                    (rec (cdr vars)
                      (cdr vals)
                      (extend-env (car vars)
                                  (car vals)
                                  env))))]))

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
    [let-exp (var exp body)
             (value-of body (extend-env var
                                        (value-of exp env)
                                        env))]
    [letrec-exp (p-name-list b-vars-list body-list exp)
                (value-of exp (extend-env-rec p-name-list b-vars-list body-list env))]

    ;;; procedures
    [proc-exp (vars exp)
              (proc-val (procedure vars exp env))]

    [call-exp (exp1 exp-list)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exp-list))]))