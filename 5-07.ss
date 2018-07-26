#lang eopl

;;; 5.7

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
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    ;;;  list  ;;;;;;;;
    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)
    
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
     ("null")
     null-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define (apply-cont cont v)
  (cont v))

(define (end-cont)
  (lambda (v)
    (eopl:printf "end of computation. ~A\n" v)
    v))

(define (zero?-cont cont)
  (lambda (v)
    (apply-cont cont
                (bool-val (zero? (expval->num v))))))

(define (let-exp-cont vars exps1 env new-env body cont)
  (lambda (val)
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
  (lambda (v)
    (if (expval->bool v)
        (value-of/k exp2 env cont)
        (value-of/k exp3 env cont))))

(define (rator-cont exp2 env cont)
  (lambda (v)
    (value-of/k exp2 env
                (rand-cont v cont))))

(define (rand-cont p cont)
  (lambda (v)
    (apply-procedure/k (expval->proc p)
                     v
                     cont)))

(define (diff1-cont exp2 env cont)
  (lambda (v)
    (value-of/k exp2 env
                (diff2-cont v cont))))

(define (diff2-cont v1 cont)
  (lambda (v)
    (apply-cont cont
                (num-val (-
                          (expval->num v1)
                          (expval->num v))))))

(define (null?-cont cont)
  (lambda (v)
    (apply-cont cont (bool-val (expval-null? v)))))

(define (cons-car-cont exp2 env cont)
  (lambda (val1)
    (value-of/k exp2 env
                (cons-cdr-cont val1 cont))))

(define (cons-cdr-cont val1 cont)
  (lambda (val2)
    (apply-cont cont (cons-val (cons val1 val2)))))

(define (car-cont cont)
  (lambda (val1)
    (apply-cont cont (car (expval->cons val1)))))

(define (cdr-cont cont)
  (lambda (val1)
    (apply-cont cont (cdr (expval->cons val1)))))

(define (list-cont exps env lst cont)
  (lambda (val1)
    (if (null? exps)
        (apply-cont cont (list-val (reverse (cons val1 lst))))
        (value-of/k (car exps) env
                    (list-cont (cdr exps) env
                               (cons val1 lst)
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
   (b-var identifier?)
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
   (var identifier?)
   (body expression?)
   (env environment?)))

(define (apply-procedure/k p val cont)
  (cases proc p
    [procedure (var body env)
               (value-of/k body
                         (extend-env var val env)
                         cont)]))

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

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
      (value-of/k exp (empty-env) (end-cont))]))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (apply-cont cont (num-val num))]
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (diff1-cont exp2 env cont))]
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
    [letrec-exp (p-name b-var body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-var body env) cont)]

    ;;; procedures
    [proc-exp (var exp1)
              (apply-cont cont (proc-val (procedure var exp1 env)))]

    [call-exp (exp1 exp2)
              (value-of/k exp1 env
                          (rator-cont exp2 env cont))]

    ;;;;;;; list
    [null-exp ()
              (apply-cont cont (null-val))]
    [null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont))]
    [cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (cons-car-cont exp2 env cont))]
    [car-exp (exp1)
             (value-of/k exp1 env
                         (car-cont cont))]
    [cdr-exp (exp1)
             (value-of/k exp1 env
                         (cdr-cont cont))]

    [list-exp (exps)
              (if (null? exps)
                  (apply-cont cont (list-val '()))
                  (value-of/k (car exps) env
                              (list-cont (cdr exps) env '() cont)))]
  ))