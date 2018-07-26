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
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)

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
      (value-of/k exp (empty-env)
                  (lambda (val)
                    (eopl:printf "end of computation.~%")
                    val))]))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (cont (num-val num))]
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (lambda (val1)
                            (value-of/k exp2 env
                                        (lambda (val2)
                                          (cont (num-val (-
                                                          (expval->num val1)
                                                          (expval->num val2))))))))]
    [var-exp (var)
      (cont (apply-env env var))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (lambda (val1)
                    (cont (bool-val (zero? (expval->num val1))))))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                        (lambda (val1)
                          (value-of/k (if (expval->bool val1)
                                          exp2
                                          exp3)
                                      env
                                      cont)))]
    [let-exp (var exp1 body)
             (value-of/k exp1 env
                         (lambda (val1)
                           (value-of/k body
                                       (extend-env var val1 env)
                                       cont)))]
    [letrec-exp (p-name b-var body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-var body env) cont)]

    ;;; procedures
    [proc-exp (var exp1)
              (cont (proc-val (procedure var exp1 env)))]

    [call-exp (exp1 exp2)
              (value-of/k exp1 env
                          (lambda (val1)
                            (value-of/k exp2 env
                                        (lambda (val2)
                                          (apply-procedure/k (expval->proc val1) val2 cont)))))]
  ))