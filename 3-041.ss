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
    
    (expression (identifier) var-exp)

    ;;;;;;;;;;;;;;;;; arith ;;;;;;;;;;;;;;;;;;;;;;;;
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    
    (expression
     ("+" "(" expression "," expression ")")
     add-exp)
    
    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)
    
    (expression
     ("/" "(" expression "," expression ")")
     div-exp)
    
    (expression
     ("minus" "(" expression ")")
     minus-exp)
    
    (expression
     ("print" "(" expression ")")
     print-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("=" "(" expression "," expression ")")
     equal?-exp)
    
    (expression
     (">" "(" expression "," expression ")")
     greater?-exp)
    
    (expression
     ("<" "(" expression "," expression ")")
     less?-exp)
    ;;;;;;;;;;;;;;;;;;; control ;;;;;;;;;;;;;;;;
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)
    
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)
    
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;;;;;;;;;;;;;;;;;; list ;;;;;;;;;;;;;
    
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
     emptylist-exp)
    
    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    ;;;;;;;;;;;;;;;;;; nameless ;;;;;;;;;;;;;;;;;;
    
    (expression
     ("%lexref" number number)
     nl-var-exp)
    
    (expression
     ("%let" (arbno expression) "in" expression)
     nl-let-exp)
    
    (expression
     ("%lexproc" expression)
     nl-proc-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;; nameless environment ;;;;;;;;;;;;;

(define (nl-environment? x)
  ((list-of (list-of expval?)) x))

(define (empty-nl-env)
  '())

(define (extend-nl-env val env)
  (cons (list val) env))

(define (extend-nl-env* val-list env)
  (cons val-list env))

(define (apply-nl-env env n p)
  (list-ref (list-ref env n) p))

;;;;;;;;;;;;;;; static environment ;;;;;;;;;;;;;;

(define (empty-senv)
  '())

(define (extend-senv var env)
  (cons (list var) env))

(define (extend-senv* var-list env)
  (cons var-list env))

(define (apply-senv env var)
  (let loop1 ([e env]
              [n 0])
    (if (null? e)
        (eopl:error 'apply-senv "variable ~s is not bound" var)
        (let loop2 ([ls (car e)]
                    [p 0])
          (cond
            [(null? ls)
             (loop1 (cdr e) (+ n 1))]
            [(eqv? (car ls) var)
             (cons n p)]
            [else
             (loop2 (cdr ls) (+ p 1))])))))

;;;;;;;;;;;;;;; translator ;;;;;;;;;;;;;;;

(define (translation-of-program prg)
  (cases program prg
    [a-program (exp)
               (a-program
                (translation-of exp (empty-senv)))]))

(define (translation-of-list ls senv)
  (let loop ([ls ls])
    (if (null? ls)
        '()
        (cons (translation-of (car ls) senv)
              (translation-of-list (cdr ls) senv)))))

(define (translation-of exp senv)
  (cases expression exp
    [const-exp (num)
               (const-exp num)]
    [emptylist-exp ()
                   (emptylist-exp)]
    [diff-exp (exp1 exp2)
              (diff-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [add-exp (exp1 exp2)
             (add-exp (translation-of exp1 senv)
                      (translation-of exp2 senv))]
    [mult-exp (exp1 exp2)
              (mult-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [div-exp (exp1 exp2)
             (div-exp (translation-of exp1 senv)
                      (translation-of exp2 senv))]
    [equal?-exp (exp1 exp2)
                (equal?-exp (translation-of exp1 senv)
                            (translation-of exp2 senv))]
    [greater?-exp (exp1 exp2)
                  (greater?-exp (translation-of exp1 senv)
                                (translation-of exp2 senv))]
    [less?-exp (exp1 exp2)
               (less?-exp (translation-of exp1 senv)
                          (translation-of exp2 senv))]
    [zero?-exp (exp1)
               (zero?-exp (translation-of exp1 senv))]
    [car-exp (exp1)
             (car-exp (translation-of exp1 senv))]
    [cdr-exp (exp1)
             (cdr-exp (translation-of exp1 senv))]
    [null?-exp (exp1)
               (null?-exp (translation-of exp1 senv))]
    [minus-exp (exp1)
               (minus-exp (translation-of exp1 senv))]
    [print-exp (exp1)
               (print-exp (translation-of exp1 senv))]
    [cons-exp (exp1 exp2)
              (cons-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [list-exp (exps)
              (list-exp (translation-of-list exps senv))]
    [if-exp (exp1 exp2 exp3)
            (if-exp (translation-of exp1 senv)
                    (translation-of exp2 senv)
                    (translation-of exp3 senv))]
    [var-exp (var)
             (let ([pos (apply-senv senv var)])
               (nl-var-exp (car pos) (cdr pos)))]
    [let-exp (var-list exp-list body)
             (nl-let-exp (translation-of-list exp-list senv)
                         (translation-of body
                                         (extend-senv* var-list senv)))]
    [proc-exp (var-list body)
              (nl-proc-exp (translation-of body
                                           (extend-senv* var-list senv)))]
    [call-exp (exp1 exp-list)
              (call-exp (translation-of exp1 senv)
                        (translation-of-list exp-list senv))]
    [else
     (eopl:error 'translation-of "invalid expression ~A" exp)]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (body expression?)
   (env nl-environment?)))

(define (apply-procedure p val-list)
  (cases proc p
    [procedure (body env)
               (value-of body
                         (extend-nl-env* val-list env))]))

;;;;;;;;;;;;;;  expval    ;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (cons-val
   (car expval?)
   (cdr expval?))
  (null-val))

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

(define (expval->car val)
  (cases expval val
    [cons-val (car cdr) car]
    [else
     (eopl:error 'expval->car "expval ~A is not cons" val)]))

(define (expval->cdr val)
  (cases expval val
    [cons-val (car cdr) cdr]
    [else
     (eopl:error 'expval->cdr "expval ~A is not cons" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (expval-cons? val)
  (cases expval val
    [cons-val (car cdr) #t]
    [else #f]))

;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (value-of-program
   (translation-of-program
    (scan&parse prog))))

(define (value-of-program prg)
  (cases program prg
    [a-program (exp)
               (value-of exp (empty-nl-env))]))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
               (num-val num)]
    [diff-exp (exp1 exp2)
              (value-of-arith - env exp1 exp2)]
    [add-exp (exp1 exp2)
             (value-of-arith + env exp1 exp2)]
    [mult-exp (exp1 exp2)
              (value-of-arith * env exp1 exp2)]
    [div-exp (exp1 exp2)
             (value-of-arith quotient env exp1 exp2)]
    
    [equal?-exp (exp1 exp2)
                (value-of-arith = env exp1 exp2)]
    [greater?-exp (exp1 exp2)
                  (value-of-arith > env exp1 exp2)]
    [less?-exp (exp1 exp2)
               (value-of-arith < env exp1 exp2)]
    
    [minus-exp (exp)
               (value-of-arith - env exp)]
    [zero?-exp (exp)
               (value-of-arith zero? env exp)]
    
    #|[var-exp (var)
      (apply-env env var)]|#
    [nl-var-exp (n p)
                (apply-nl-env env n p)]
    [if-exp (exp1 exp2 exp3)
            (if (expval->bool (value-of exp1 env))
                (value-of exp2 env)
                (value-of exp3 env))]
    #|[let-exp (var exp body)
             (value-of body (extend-env var
                                        (value-of exp env)
                                        env))]|#
    [nl-let-exp (exp-list body)
                (value-of body
                          (extend-nl-env* (value-of-list exp-list env) env))]
    
    ;;; procedures
    #|[proc-exp (var exp)
              (proc-val (procedure var exp env))]|#
    
    [nl-proc-exp (exp)
                 (proc-val (procedure exp env))]
    
    [call-exp (exp1 exp-list)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of-list exp-list env))]
    
    ;;; list
    [cons-exp (exp1 exp2)
              (cons-val (value-of exp1 env)
                        (value-of exp2 env))]
    [car-exp (exp)
             (expval->car
              (value-of exp env))]
    [cdr-exp (exp)
             (expval->cdr
              (value-of exp env))]
    [null?-exp (exp)
               (bool-val (expval-null?
                          (value-of exp env)))]
    [emptylist-exp ()
                   (null-val)]
    
    [list-exp (list)
              (letrec ([rec (lambda (ls)
                              (if (null? ls)
                                  (null-val)
                                  (cons-val (value-of (car ls) env)
                                            (rec (cdr ls)))))])
                (rec list))]
    
    [print-exp (exp)
               (letrec ([rec (lambda (val need-par)
                               (cases expval val
                                 [null-val ()
                                           (display "()")]
                                 [bool-val (bool)
                                           (display bool)]
                                 [num-val (num)
                                          (display num)]
                                 [cons-val (car cdr)
                                           (when need-par (display "("))
                                           (rec car #t)
                                           (cond
                                             [(expval-null? cdr)
                                              (display ")")]
                                             [(expval-cons? cdr)
                                              (display " ")
                                              (rec cdr #f)]
                                             [else
                                              (display " . ")
                                              (rec cdr #f)
                                              (display ")")])]
                                 [proc-val (exp)
                                           (display "#procedure")]))])
                 (rec (value-of exp env) #t)
                 (newline)
                 (num-val 1))]
    
    [else
     (eopl:error 'value-of "invalid expression ~A" exp)]))

(define (value-of-list ls env)
  (if (null? ls)
      '()
      (cons (value-of (car ls) env)
            (value-of-list (cdr ls) env))))

(define (value-of-arith op env . exps)
  (let ([val (apply op (map (lambda (x)
                              (expval->num (value-of x env)))
                            exps))])
    ((cond
       [(number? val)
        num-val]
       [(boolean? val)
        bool-val]
       [else
        (eopl:error 'value-of-arith "invalid result type ~A" val)])
     val)))