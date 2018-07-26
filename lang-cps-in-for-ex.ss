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
     ("*" "(" expression "," expression ")")
     mult-exp)

    (expression
     ("add1" "(" expression ")")
     add1-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("number?" "(" expression ")")
     number?-exp)
    
    (expression
     ("equal?" "(" expression "," expression ")")
     equal?-exp)
    
    (expression
     ("less?" "(" expression "," expression ")")
     less?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
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
     ("true")
     true-exp)

    (expression
     ("false")
     false-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    ;; print
    (expression
     ("print" "(" (separated-list expression ",") ")")
     print-exp)

    (expression
     ("begin" expression ";" (arbno expression ";") "end")
     begin-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define-datatype continuation continuation?
  [end-cont]
  [zero-cont
   (cont continuation?)]
  [add1-cont
   (cont continuation?)]
  [number-cont
   (cont continuation?)]
  [let-exp-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (env environment?)
   (new-env environment?)
   (body expression?)
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
  [binary1-cont
   (op procedure?)
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [binary2-cont
   (op procedure?)
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
  [cmp1-cont
   (pred procedure?)
   (exp2 expression?)
   (env environment?)
   (cont1 continuation?)]
  [cmp2-cont
   (pred procedure?)
   (val1 expval?)
   (cont1 continuation?)]
  [print-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [begin-cont
    (exps (list-of expression?))
    (env environment?)
    (cont continuation?)]
  )

(define (apply-cont cont v)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ")
     (print-val v)
     v]
    [zero-cont (cont1)
                (apply-cont cont1
                            (bool-val (zero? (expval->num v))))]
    [add1-cont (cont1)
               (apply-cont cont1
                           (num-val (+ 1 (expval->num v))))]
    [number-cont (cont1)
                 (apply-cont cont1
                             (bool-val (expval-num? v)))]
    [cmp1-cont (pred exp2 env cont1)
               (value-of/k exp2 env
                           (cmp2-cont pred v cont1))]
    [cmp2-cont (pred val1 cont1)
               (apply-cont cont1 (bool-val (pred
                                            (expval->num val1)
                                            (expval->num v))))]
    [if-test-cont (exp2 exp3 env cont1)
                  (if (expval->bool v)
                      (value-of/k exp2 env cont1)
                      (value-of/k exp3 env cont1))]
    [let-exp-cont (vars exps1 env new-env body cont1)
                  (if (null? exps1)
                      (value-of/k body
                                  (extend-env (car vars) v new-env)
                                  cont1)
                      (value-of/k (car exps1)
                                  env
                                  (let-exp-cont (cdr vars)
                                                (cdr exps1)
                                                env
                                                (extend-env (car vars) v new-env)
                                                body
                                                cont1)))]
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
    [binary1-cont (op exp2 env cont1)
                  (value-of/k exp2 env
                              (binary2-cont op v cont1))]
    [binary2-cont (op val cont1)
                  (apply-cont cont1
                              (num-val (op
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
    [print-cont (exps env cont1)
                (letrec ([disp (lambda (v need-par)
                                 (cases expval v
                                   [bool-val (b)
                                             (display (if b
                                                          "true"
                                                          "false"))]
                                   [num-val (n)
                                            (display n)]
                                   [proc-val (proc)
                                             (display "#procedure")]
                                   [null-val ()
                                             (display "()")]
                                   [pair-val (pair)
                                             (when need-par
                                               (display "("))
                                             (disp (car pair) #t)
                                             (cases expval (cdr pair)
                                               [null-val ()
                                                         (display ")")]
                                               [pair-val (p)
                                                         (display " ")
                                                         (disp (cdr pair) #f)]
                                               [else
                                                (begin
                                                  (display " . ")
                                                  (disp (cdr pair) #f)
                                                  (display ")"))])]))])
                  (disp v #t)
                  (if (null? exps)
                      (begin
                        (newline)
                        (apply-cont cont1 (num-val 1)))
                      (begin
                        (display "\t")
                        (value-of/k (car exps) env
                                    (print-cont (cdr exps) env cont1)))))]
    [begin-cont (exps env cont1)
                (if (null? exps)
                    (apply-cont cont1 v)
                    (value-of/k (car exps) env
                                (begin-cont (cdr exps) env cont1)))]
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
               (when (not (= (length vars) (length vals)))
                 (eopl:error 'apply-procedure/k
                             "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length vals)))
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

(define (expval-num? val)
  (cases expval val
    [num-val (num) #t]
    [else #f]))

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
                          (binary1-cont - exp2 env cont))]
    [mult-exp (exp1 exp2)
              (value-of/k exp1 env
                          (binary1-cont * exp2 env cont))]
    [add1-exp (exp1)
              (value-of/k exp1 env
                          (add1-cont cont))]
    [var-exp (var)
      (apply-cont cont (apply-env env var))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (zero-cont cont))]
    [number?-exp (exp1)
      (value-of/k exp1 env
                  (number-cont cont))]
    [equal?-exp (exp1 exp2)
               (value-of/k exp1 env
                           (cmp1-cont = exp2 env cont))]
    [less?-exp (exp1 exp2)
              (value-of/k exp1 env
                          (cmp1-cont < exp2 env cont))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                      (if-test-cont exp2 exp3 env cont))]
    [let-exp (vars exps body)
             (if (null? vars)
                 (eopl:error 'value-of/k "invalid let expression: ~A" exp)
                 (value-of/k (car exps) env
                             (let-exp-cont vars (cdr exps) env env body cont)))]
    [letrec-exp (p-names b-varss bodies exp1)
                (value-of/k exp1 (extend-env-rec* p-names b-varss bodies env) cont)]

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
    [true-exp ()
              (apply-cont cont (bool-val #t))]
    [false-exp ()
               (apply-cont cont (bool-val #f))]

    ;; print
    [print-exp (exps)
               (if (null? exps)
                   (begin
                     (newline)
                     (apply-cont cont (num-val 1)))
                   (value-of/k (car exps) env
                               (print-cont (cdr exps) env cont)))]
    [begin-exp (exp1 exps)
                   (value-of/k exp1 env
                               (begin-cont exps env cont))]
  ))

(provide run)