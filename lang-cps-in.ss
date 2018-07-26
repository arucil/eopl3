#lang eopl

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
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [rand-cont
   (exps (list-of expression?))
   (env environment?)
   (vals (list-of expval?))
   (proc expval?)
   (cont continuation?)]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [diff2-cont
   (val1 expval?)
   (cont continuation?)]
  )

(define (apply-cont cont v)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ~%")
     v]
    [zero?-cont (cont1)
                (apply-cont cont1
                            (bool-val (zero? (expval->num v))))]
    [if-test-cont (exp2 exp3 env cont1)
                  (if (expval->bool v)
                      (value-of/k exp2 env cont1)
                      (value-of/k exp3 env cont1))]
    [let-exp-cont (var body env cont1)
                  (value-of/k body
                              (extend-env var v env)
                              cont1)]
    [rator-cont (exps env cont1)
                (if (null? exps)
                    (apply-procedure/k (expval->proc v)
                                       '()
                                       cont1)
                    (value-of/k (car exps) env
                                (rand-cont (cdr exps) env '() v cont1)))]
    [rand-cont (exps env vals val1 cont1)
               (if (null? exps)
                   (apply-procedure/k (expval->proc val1)
                                      (reverse (cons v vals))
                                      cont1)
                   (value-of/k (car exps)
                               env
                               (rand-cont (cdr exps) env
                                          (cons v vals)
                                          val1 cont1)))]
    [diff1-cont (exp2 env cont1)
                (value-of/k exp2 env
                            (diff2-cont v cont1))]
    [diff2-cont (val cont1)
                (apply-cont cont1
                            (num-val (-
                                      (expval->num val)
                                      (expval->num v))))]
    ))

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
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-vars (list-of (list-of identifier?)))
   (bodies (list-of expression?))
   (env environment?)))

(define (extend-env* vars vals env)
  (let loop ([vars vars]
             [vals vals]
             [e env])
    (if (null? vars)
        e
        (loop (cdr vars)
              (cdr vals)
              (extend-env (car vars)
                          (car vals)
                          e)))))

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
                        (apply-env e svar))]
    [extend-env-rec* (pnames bvars bodies e)
                     (let loop ([pnames pnames]
                                [bvars bvars]
                                [bodies bodies])
                       (cond
                         [(null? pnames)
                          (apply-env e svar)]
                         [(eqv? (car pnames) svar)
                          (proc-val (procedure (car bvars) (car bodies) env))]
                         [else
                          (loop (cdr pnames)
                                (cdr bvars)
                                (cdr bodies))]))]
    ))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure/k p vals cont)
  (cases proc p
    [procedure (vars body env)
               (letrec ([rec (lambda (vars vals e)
                               (if (null? vars)
                                   e
                                   (rec (cdr vars)
                                     (cdr vals)
                                     (extend-env (car vars)
                                                 (car vals)
                                                 e))))])
                 (value-of/k body
                             (rec vars vals env)
                             cont))]))

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
    [let-exp (var exp1 body)
             (value-of/k exp1 env
                       (let-exp-cont var body env cont))]
    [letrec-exp (p-names b-varss bodies exp1)
                (value-of/k exp1 (extend-env-rec* p-names b-varss bodies env) cont)]

    ;;; procedures
    [proc-exp (vars exp1)
              (apply-cont cont (proc-val (procedure vars exp1 env)))]

    [call-exp (exp1 exps)
              (value-of/k exp1 env
                          (rator-cont exps env cont))]
  ))

(provide run)