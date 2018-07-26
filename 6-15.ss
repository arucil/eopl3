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
  '((cps-program (cps-tf-exp) cps-a-program)

    ;;; simple
    (cps-simple-exp
     (number)
     cps-const-exp)

    (cps-simple-exp
     (identifier)
     cps-var-exp)

    (cps-simple-exp
     ("-" "(" cps-simple-exp "," cps-simple-exp ")")
     cps-diff-exp)

    (cps-simple-exp
     ("zero?" "(" cps-simple-exp ")")
     cps-zero?-exp)

    (cps-simple-exp
     ("proc" "(" (separated-list identifier ",") ")" cps-tf-exp)
     cps-proc-exp)

    ;; tail form
    (cps-tf-exp
     (cps-simple-exp)
     simple-exp->exp)

    (cps-tf-exp
     ("let" identifier "=" cps-simple-exp "in" cps-tf-exp)
     cps-let-exp)

    (cps-tf-exp
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" cps-tf-exp) "in" cps-tf-exp)
     cps-letrec-exp)

    (cps-tf-exp
     ("if" cps-simple-exp "then" cps-tf-exp "else" cps-tf-exp)
     cps-if-exp)

    (cps-tf-exp
     ("(" cps-simple-exp (arbno cps-simple-exp) ")")
     cps-call-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

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
   (body cps-tf-exp?)
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-vars (list-of (list-of identifier?)))
   (bodies (list-of cps-tf-exp?))
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
   (body cps-tf-exp?)
   (env environment?)))

(define (apply-procedure/k p vals)
  (cases proc p
    [procedure (vars body env)
                 (value-of/k body
                             (extend-env* vars vals env))]))

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
  (cases cps-program (scan&parse prog)
    [cps-a-program (exp)
      (value-of/k exp (empty-env))]))

(define (value-of/k exp env)
  (cases cps-tf-exp exp
    [simple-exp->exp (simple)
                     (value-of-simple-exp simple env)]
    [cps-let-exp (var rhs body)
                 (value-of/k body
                             (extend-env var
                                         (value-of-simple-exp rhs env)
                                         env))]
    [cps-letrec-exp (p-names b-varss p-bodies body)
                    (value-of/k body
                                (extend-env-rec* p-names b-varss p-bodies env))]
    [cps-if-exp (simple1 exp1 exp2)
                (if (expval->bool (value-of-simple-exp simple1 env))
                    (value-of/k exp1 env)
                    (value-of/k exp2 env))]
    [cps-call-exp (rator rands)
                  (apply-procedure/k (expval->proc
                                      (value-of-simple-exp rator env))
                                     (map (lambda (x)
                                            (value-of-simple-exp x env))
                                          rands))]
    ))

(define (value-of-simple-exp exp env)
  (cases cps-simple-exp exp
    [cps-const-exp (num)
                   (num-val num)]
    [cps-var-exp (var)
                 (apply-env env var)]
    [cps-diff-exp (simple1 simple2)
                  (num-val (- (expval->num (value-of-simple-exp simple1 env))
                              (expval->num (value-of-simple-exp simple2 env))))]
    [cps-zero?-exp (simple1)
                   (bool-val (zero? (expval->num (value-of-simple-exp simple1 env))))]
    [cps-proc-exp (vars body)
                  (proc-val (procedure vars body env))]
    ))

(provide run)