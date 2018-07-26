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

(define (continuation?? v)
  (or (continuation? v)
      (boolean? v)))

(define-datatype continuation continuation?
  [end-cont]
  [zero?-cont
   (cont continuation?)
   (try continuation??)]
  [let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [rator-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [rand-cont
   (proc expval?)
   (cont continuation?)
   (try continuation??)]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [diff2-cont
   (val1 expval?)
   (cont continuation?)
   (try continuation??)]
  [null?-cont
   (cont continuation?)
   (try continuation??)]
  [cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [cons2-cont
   (val1 expval?)
   (cont continuation?)
   (try continuation??)]
  [car-cont
   (cont continuation?)
   (try continuation??)]
  [cdr-cont
   (cont continuation?)
   (try continuation??)]
  [list-cont
   (exp-list (list-of expression?))
   (env environment?)
   (val-list (list-of expval?))
   (cont continuation?)
   (try continuation??)]
  [try-cont
   (var identifier?)
   (exp1 expression?)
   (env environment?)
   (cont continuation?)
   (try continuation??)]
  [raise-cont
   (cont continuation?)
   (try continuation??)]
  )

(define (apply-cont cont v)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ")
     (print-val v)
     v]
    [zero?-cont (cont1 h)
                (apply-cont cont1
                            (bool-val (zero? (expval->num v))))]
    [if-test-cont (exp2 exp3 env cont1 h)
                  (if (expval->bool v)
                      (value-of/k exp2 env cont1)
                      (value-of/k exp3 env cont1))]
    [let-exp-cont (var body env cont1 h)
                  (value-of/k body
                              (extend-env var v env)
                              cont1)]
    [rator-cont (exp2 env cont1 h)
                (value-of/k exp2 env
                            (rand-cont v cont1 (get-handler cont1)))]
    [rand-cont (val cont1 h)
               (apply-procedure/k (expval->proc val)
                                  v
                                  cont1)]
    [diff1-cont (exp2 env cont1 h)
                (value-of/k exp2 env
                            (diff2-cont v cont1 (get-handler cont1)))]
    [diff2-cont (val cont1 h)
                (apply-cont cont1
                            (num-val (-
                                      (expval->num val)
                                      (expval->num v))))]
    [null?-cont (cont1 h)
                (apply-cont cont1 (bool-val (expval-null? v)))]
    [cons1-cont (exp2 env cont1 h)
                (value-of/k exp2 env
                            (cons2-cont v cont1 (get-handler cont1)))]
    [cons2-cont (val1 cont1 h)
                (apply-cont cont1 (pair-val (cons val1 v)))]
    [car-cont (cont1 h)
              (apply-cont cont1 (car (expval->pair v)))]
    [cdr-cont (cont1 h)
              (apply-cont cont1 (cdr (expval->pair v)))]
    [list-cont (exp-list env val-list cont1 h)
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
                                          cont1 (get-handler cont1))))]
    [try-cont (var exp2 env cont1 h)
              (apply-cont cont1 v)]
    [raise-cont (cont1 h)
                (apply-handler v (get-handler cont1))]
    ))

(define (apply-handler val cont)
  (if cont
      (cases continuation cont
        [try-cont (var exp2 env cont1 h)
                  (value-of/k exp2
                              (extend-env var val env)
                              cont1)]
        [else
         (eopl:error 'apply-handler "unreachable ~A" cont)])
      (eopl:error 'apply-handler "uncaught exception ~A" val)))

(define (get-handler cont)
  (cases continuation cont
    [end-cont () #f]
    [zero?-cont (cont1 h)
                h]
    [if-test-cont (exp2 exp3 env cont1 h)
                  h]
    [let-exp-cont (var body env cont1 h)
                  h]
    [rator-cont (exp2 env cont1 h)
                h]
    [rand-cont (val1 cont1 h)
               h]
    [diff1-cont (exp2 env cont1 h)
                h]
    [diff2-cont (val1 cont1 h)
                h]
    [null?-cont (cont1 h)
                h]
    [cons1-cont (exp2 env cont1 h)
                h]
    [cons2-cont (val1 cont1 h)
                h]
    [car-cont (cont1 h)
              h]
    [cdr-cont (cont1 h)
              h]
    [list-cont (exps env vals cont1 h)
               h]
    [try-cont (var exp2 env cont1 h)
              cont]
    [raise-cont (cont1 h)
                h]))

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
                          (diff1-cont exp2 env cont (get-handler cont)))]
    [var-exp (var)
      (apply-cont cont (apply-env env var))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (zero?-cont cont (get-handler cont)))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                      (if-test-cont exp2 exp3 env cont (get-handler cont)))]
    [let-exp (var exp1 body)
             (value-of/k exp1 env
                       (let-exp-cont var body env cont (get-handler cont)))]
    [letrec-exp (p-name b-var body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-var body env) cont)]

    ;;; procedures
    [proc-exp (var exp1)
              (apply-cont cont (proc-val (procedure var exp1 env)))]

    [call-exp (exp1 exp2)
              (value-of/k exp1 env
                          (rator-cont exp2 env cont (get-handler cont)))]

    ;;; list
    [null-exp ()
              (apply-cont cont (null-val) (get-handler cont))]
    [null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont (get-handler cont)))]
    [cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (cons1-cont exp2 env cont (get-handler cont)))]
    [car-exp (exp1)
             (value-of/k exp1 env
                         (car-cont cont (get-handler cont)))]
    [cdr-exp (exp1)
             (value-of/k exp1 env
                         (cdr-cont cont (get-handler cont)))]
    [list-exp (exp-list)
              (if (null? exp-list)
                  (apply-cont cont (null-val))
                  (value-of/k (car exp-list) env
                              (list-cont (cdr exp-list)
                                         env
                                         '()
                                         cont (get-handler cont))))]

    ;;; exception
    [try-exp (exp1 var exp2)
             (value-of/k exp1 env
                         (try-cont var exp2 env cont (get-handler cont)))]
    [raise-exp (exp1)
               (value-of/k exp1 env
                           (raise-cont cont (get-handler cont)))]
  ))