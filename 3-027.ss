#lang eopl

;;; 3.27

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
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("traceproc" "(" identifier ")" expression)
     traceproc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (env environment?)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (traceproc-val
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

(define (apply-procedure p val)
  (cases proc p
    [procedure (var body env)
               (value-of body
                         (extend-env var val env))]))

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

    ;;; procedures
    [proc-exp (var exp)
              (proc-val (procedure var
                                   exp
                                   (build-free-var-env
                                    (get-free-vars exp (list var))
                                    env)))]

    [traceproc-exp (var exp)
                   (traceproc-val (procedure var
                                             exp
                                             (build-free-var-env
                                              (get-free-vars exp (list var))
                                              env)))]

    [call-exp (exp1 exp2)
              (let ([p (value-of exp1 env)]
                    [arg (value-of exp2 env)])
                (cases expval p
                  [proc-val (proc)
                            (apply-procedure proc arg)]
                  [traceproc-val (proc)
                                 (eopl:printf "enter procedure ~A\n" proc)
                                 (let ([ret (apply-procedure proc arg)])
                                   (eopl:printf "leave procedure ~A\n" proc)
                                   ret)]
                  [else
                   (eopl:error 'value-of "expval ~A is not procedure" p)]))]))

(define (exists? list val)
  (cond
    [(null? list) #f]
    [(eqv? (car list) val) #t]
    [else (exists? (cdr list) val)]))

(define (build-free-var-env free-vars env)
  (if (null? free-vars)
      (empty-env)
      (extend-env (car free-vars)
                  (apply-env env (car free-vars))
                  (build-free-var-env (cdr free-vars) env))))

(define (get-free-vars exp var-list)
  (cases expression exp
    [const-exp (n) '()]
    [var-exp (var)
             (if (exists? var-list var)
                 '()
                 (list var))]
    [diff-exp (exp1 exp2)
              (append (get-free-vars exp1 var-list)
                      (get-free-vars exp2 var-list))]
    [zero?-exp (exp)
           (get-free-vars exp var-list)]
    [if-exp (exp1 exp2 exp3)
            (append (get-free-vars exp1 var-list)
                    (get-free-vars exp2 var-list)
                    (get-free-vars exp3 var-list))]
    [let-exp (var exp body)
             (append (get-free-vars exp var-list)
                     (get-free-vars body (cons var var-list)))]
    [proc-exp (var body)
          (get-free-vars body (cons var var-list))]
    [traceproc-exp (var body)
                   (get-free-vars body (cons var var-list))]
    [call-exp (exp1 exp2)
              (append (get-free-vars exp1 var-list)
                      (get-free-vars exp2 var-list))]))