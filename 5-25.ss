#lang eopl

;;; 5.25

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

;;;;;;;;;;;;;;  globals  ;;;;;;;;;;;;

(define cont 'a)
(define exp 'a)
(define env 'a)
(define val 'a)
(define proc1 'a)
(define args 'a)

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define-datatype continuation continuation?
  [end-cont]
  [zero?-cont
   (cont continuation?)]
  [let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?)]
  [if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)]
  [rator-cont
   (exp-list (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [rand-cont
   (proc expval?)
   (exp-list (list-of expression?))
   (val-list (list-of expval?))
   (cont continuation?)]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [diff2-cont
   (val1 expval?)
   (cont continuation?)])

(define (apply-cont)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ~A\n" val)
     val]
    [zero?-cont (cont1)
                (set! val (bool-val (zero? (expval->num val))))
                (set! cont cont1)
                (apply-cont)]
    [if-test-cont (exp2 exp3 senv cont1)
                  (set! cont cont1)
                  (set! exp (if (expval->bool val)
                                exp2
                                exp3))
                  (set! env senv)
                  (value-of/k)]
    [let-exp-cont (var body senv cont1)
                  (set! cont cont1)
                  (set! env (extend-env var val senv))
                  (set! exp body)
                  (value-of/k)]
    [rator-cont (exp-list senv cont1)
                (if (null? exp-list)
                    (begin
                      (set! cont cont1)
                      (set! args '())
                      (set! proc1 (expval->proc val))
                      (apply-procedure/k))
                    (begin
                      (set! exp (car exp-list))
                      (set! env senv)
                      (set! cont (rand-cont val (cdr exp-list) '() cont1))
                      (value-of/k)))]
    [rand-cont (val1 exp-list val-list cont1)
               (if (null? exp-list)
                   (begin
                     (set! cont cont1)
                     (set! args (reverse (cons val val-list)))
                     (set! proc1 (expval->proc val1))
                     (apply-procedure/k))
                   (begin
                     (set! exp (car exp-list))
                     (set! cont (rand-cont val1
                                           (cdr exp-list)
                                           (cons val val-list)
                                           cont1))
                     (value-of/k)))]
    [diff1-cont (exp2 senv cont1)
                (set! exp exp2)
                (set! env senv)
                (set! cont (diff2-cont val cont1))
                (value-of/k)]
    [diff2-cont (val1 cont1)
                (set! cont cont1)
                (set! val (num-val (-
                                    (expval->num val1)
                                    (expval->num val))))
                (apply-cont)]
    ))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define (empty-env) '())

(define (environment? v)
  (list? v))

(define (extend-env var val env)
  (cons (cons var val) env))

(define (apply-env env svar)
  (cond
    [(null? env)
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [(eqv? (caar env) svar)
     (cdar env)]
    [else
     (apply-env (cdr env) svar)]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure/k)
  (cases proc proc1
    [procedure (vars body senv)
               (when (not (= (length vars) (length args)))
                 (eopl:error 'apply-procedure/k
                             "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length args)))
               (let loop ([var-list vars]
                          [val-list args])
                 (unless (null? var-list)
                   (set! env (extend-env (car var-list)
                                         (car val-list)
                                         env))
                   (loop (cdr var-list)
                         (cdr val-list))))
               (set! exp body)
               (value-of/k)]))

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp1)
               (set! exp exp1)
               (set! cont (end-cont))
               (set! env (empty-env))
               (value-of/k)]))

(define (value-of/k)
  (cases expression exp
    [const-exp (num)
               (set! val (num-val num))
               (apply-cont)]
    [diff-exp (exp1 exp2)
              (set! exp exp1)
              (set! cont (diff1-cont exp2 env cont))
              (value-of/k)]
    [var-exp (var)
             (set! val (apply-env env var))
             (apply-cont)]
    [zero?-exp (exp1)
               (set! cont (zero?-cont cont))
               (set! exp exp1)
               (value-of/k)]
    [if-exp (exp1 exp2 exp3)
            (set! cont (if-test-cont exp2 exp3 env cont))
            (set! exp exp1)
            (value-of/k)]
    [let-exp (var exp1 body)
             (set! cont (let-exp-cont var body env cont))
             (set! exp exp1)
             (value-of/k)]

    ;;; procedures
    [proc-exp (vars exp1)
              (set! val (proc-val (procedure vars exp1 env)))
              (apply-cont)]

    [call-exp (exp1 exp-list)
              (set! exp exp1)
              (set! cont (rator-cont exp-list env cont))
              (value-of/k)]
  ))