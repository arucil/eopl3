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
     ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;;; list
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

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    ;;; exception
    (expression
     ("try" expression "catch" "(" identifier ")" expression)
     try-exp)

    (expression
     ("raise" expression)
     raise-exp)
    
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
  [null?-cont
   (cont continuation?)]
  [cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [cons2-cont
   (val1 expval?)
   (cont continuation?)]
  [car-cont
   (cont continuation?)]
  [cdr-cont
   (cont continuation?)]
  [list-cont
   (exp-list (list-of expression?))
   (env environment?)
   (val-list (list-of expval?))
   (cont continuation?)]
  [try-cont
   (var identifier?)
   (exp1 expression?)
   (env environment?)
   (cont continuation?)]
  [raise-cont
   (cont continuation?)]
  )

(define (apply-cont cont v)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ")
     (print-val v)
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
    [null?-cont (cont1)
                (apply-cont cont1 (bool-val (expval-null? v)))]
    [cons1-cont (exp2 env cont1)
                (value-of/k exp2 env
                            (cons2-cont v cont1))]
    [cons2-cont (val1 cont1)
                (apply-cont cont1 (pair-val (cons val1 v)))]
    [car-cont (cont1)
              (apply-cont cont1 (car (expval->pair v)))]
    [cdr-cont (cont1)
              (apply-cont cont1 (cdr (expval->pair v)))]
    [list-cont (exp-list env val-list cont1)
               (if (null? exp-list)
                   (letrec ([make-list (lambda (ls1 val-ls)
                                         (if (null? val-ls)
                                             ls1
                                             (make-list (pair-val (cons (car val-ls)
                                                                        ls1))
                                                        (cdr val-ls))))])
                     (apply-cont cont1
                                 (make-list (null-val)
                                            (cons v val-list))))
                   (value-of/k (car exp-list)
                               env
                               (list-cont (cdr exp-list)
                                          env
                                          (cons v val-list)
                                          cont1)))]
    [try-cont (var exp2 env cont1)
              (apply-cont cont1 v)]
    [raise-cont (cont1)
                (apply-handler v cont1)]
    ))

(define (apply-handler val cont)
  (cases continuation cont
    [end-cont ()
     (eopl:error 'apply-handler "uncaught exception ~A" val)]
    [zero?-cont (cont1)
                (apply-handler val cont1)]
    [if-test-cont (exp2 exp3 env cont1)
                  (apply-handler val cont1)]
    [let-exp-cont (var body env cont1)
                  (apply-handler val cont1)]
    [rator-cont (exp2 env cont1)
                (apply-handler val cont1)]
    [rand-cont (a b c d cont1)
               (apply-handler val cont1)]
    [diff1-cont (exp2 env cont1)
                (apply-handler val cont1)]
    [diff2-cont (val1 cont1)
                (apply-handler val cont1)]
    [null?-cont (cont1)
                (apply-handler val cont1)]
    [cons1-cont (exp2 env cont1)
                (apply-handler val cont1)]
    [cons2-cont (val1 cont1)
                (apply-handler val cont1)]
    [car-cont (cont1)
              (apply-handler val cont1)]
    [cdr-cont (cont1)
              (apply-handler val cont1)]
    [list-cont (exps env vals cont1)
               (apply-handler val cont1)]
    [try-cont (var exp2 env cont1)
              (value-of/k exp2
                          (extend-env var val env)
                          cont1)]
    [raise-cont (cont1)
                (apply-handler val cont1)]))

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

(define (print-val v)
  (letrec ([dis (lambda (val need-par)
                  (cases expval val
                    [num-val (num)
                             (display num)]
                    [bool-val (b)
                              (display b)]
                    [proc-val (proc)
                              (display "#procedure")]
                    [null-val ()
                              (display "()")]
                    [pair-val (pair)
                              (when need-par
                                (display "("))
                              (dis (car pair) #t)
                              (cases expval (cdr pair)
                                [null-val ()
                                          (display ")")]
                                [pair-val (pair1)
                                          (display " ")
                                          (dis (cdr pair) #f)]
                                [else
                                 (begin
                                   (display " . ")
                                   (dis (cdr pair) #f)
                                   (display ")"))])]))])
    (dis v #t)
    (newline)))
                
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (null-val)
  (pair-val
   (pair pair?)))

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

(define (expval->pair val)
  (cases expval val
    [pair-val (pair) pair]
    [else
     (eopl:error 'expval->pair "expval ~A is not pair" val)]))

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
    [let-exp (var exp1 body)
             (value-of/k exp1 env
                       (let-exp-cont var body env cont))]
    [letrec-exp (p-name b-vars body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-vars body env) cont)]

    ;;; procedures
    [proc-exp (vars exp1)
              (apply-cont cont (proc-val (procedure vars exp1 env)))]

    [call-exp (exp1 exps)
              (value-of/k exp1 env
                          (rator-cont exps env cont))]

    ;;; list
    [null-exp ()
              (apply-cont cont (null-val))]
    [null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont))]
    [cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (cons1-cont exp2 env cont))]
    [car-exp (exp1)
             (value-of/k exp1 env
                         (car-cont cont))]
    [cdr-exp (exp1)
             (value-of/k exp1 env
                         (cdr-cont cont))]
    [list-exp (exp-list)
              (if (null? exp-list)
                  (apply-cont cont (null-val))
                  (value-of/k (car exp-list) env
                              (list-cont (cdr exp-list)
                                         env
                                         '()
                                         cont)))]

    ;;; exception
    [try-exp (exp1 var exp2)
             (value-of/k exp1 env
                         (try-cont var exp2 env cont))]
    [raise-exp (exp1)
               (value-of/k exp1 env
                           (raise-cont cont))]
  ))

(provide run)