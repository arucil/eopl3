#lang eopl

;;; 5.14

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
     ("*" "(" expression "," expression ")")
     mult-exp)
    
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
     ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression)
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

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define (apply-cont cont v)
  (cont v))

(define (end-cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (eopl:printf "end of computation. ~A\n" v)
    v))

(define (zero?-cont cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (apply-cont cont
                (bool-val (zero? (expval->num v))))))

(define (let-exp-cont vars exps1 env new-env body cont)
  (inc-cont)
  (lambda (val)
    (dec-cont)
    (if (null? exps1)
        (value-of/k body
                    (extend-env (car vars)
                                val
                                new-env)
                    cont)
        (value-of/k (car exps1)
                    env
                    (let-exp-cont (cdr vars)
                                  (cdr exps1)
                                  env
                                  (extend-env (car vars)
                                              val
                                              new-env)
                                  body
                                  cont)))))

(define (if-test-cont exp2 exp3 env cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (if (expval->bool v)
        (value-of/k exp2 env cont)
        (value-of/k exp3 env cont))))

(define (arith1-cont op exp2 env cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (value-of/k exp2 env
                (arith2-cont op v cont))))

(define (arith2-cont op v1 cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (apply-cont cont
                (num-val (op
                          (expval->num v1)
                          (expval->num v))))))

(define (rator-cont exp-list env cont)
  (inc-cont)
  (lambda (p)
    (dec-cont)
    (if (null? exp-list)
        (apply-procedure/k (expval->proc p) '() cont)
        (value-of/k (car exp-list) env
                    (rand-cont p
                               (cdr exp-list)
                               '()
                               env
                               cont)))))

(define (rand-cont p exp-list val-list env cont)
  (inc-cont)
  (lambda (v)
    (dec-cont)
    (if (null? exp-list)
        (apply-procedure/k (expval->proc p)
                           (reverse (cons v val-list))
                           cont)
        (value-of/k (car exp-list) env
                    (rand-cont p
                               (cdr exp-list)
                               (cons v val-list)
                               env
                               cont)))))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var val env)
                (if (eqv? var svar)
                    val
                    (apply-env env svar))]
    [extend-env-rec (pname bvar body e)
                    (if (eqv? svar pname)
                        (proc-val (procedure bvar body env))
                        (apply-env e svar))]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure/k p vals cont)
  (cases proc p
    [procedure (vars body env)
               (when (not (= (length vars) (length vals)))
                 (eopl:error 'apply-procedure/k
                             "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length vals)))
               (letrec ([rec (lambda (var-list val-list e)
                               (if (null? var-list)
                                   e
                                   (rec (cdr var-list)
                                     (cdr val-list)
                                     (extend-env (car var-list)
                                                 (car val-list)
                                                 e))))])
                 (value-of/k body (rec vars vals env) cont))]))

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (null-val)
  (cons-val
   (cons pair?))
  (list-val
   (list (list-of expval?))))

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

(define (expval->cons val)
  (cases expval val
    [cons-val (cons) cons]
    [else
     (eopl:error 'expval->cons "expval ~A is not cons" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define cont-count 0)

(define max-cont 0)

(define (init-max-cont)
  (set! max-cont 0))

(define (inc-cont)
  (set! cont-count (+ 1 cont-count))
  (when (> cont-count max-cont)
    (set! max-cont cont-count)))

(define (dec-cont)
  (set! cont-count (- cont-count 1)))

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (init-max-cont)
               (value-of/k exp (empty-env) (end-cont))
               (eopl:printf "max size of continuation: ~A\n" max-cont)]))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (apply-cont cont (num-val num))]
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (arith1-cont - exp2 env cont))]
    [mult-exp (exp1 exp2)
              (value-of/k exp1 env
                          (arith1-cont * exp2 env cont))]
    [var-exp (var)
      (apply-cont cont (apply-env env var))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (zero?-cont cont))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                      (if-test-cont exp2 exp3 env cont))]
    [let-exp (vars exps body)
             (if (null? vars)
                 (eopl:error 'value-of/k "invalid let expression: ~A" exp)
                 (value-of/k (car exps) env
                             (let-exp-cont vars (cdr exps) env env body cont)))]
    [letrec-exp (p-name b-vars body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-vars body env) cont)]

    ;;; procedures
    [proc-exp (vars exp1)
              (apply-cont cont (proc-val (procedure vars exp1 env)))]

    [call-exp (exp1 exp-list)
              (value-of/k exp1 env
                          (rator-cont exp-list env cont))]
  ))