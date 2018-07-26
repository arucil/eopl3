#lang eopl

;;; 3.42

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
     ("zero?" "(" expression ")")
     zero?-exp)
    
    ;;;;;;;;;;;;;;;;;;; control ;;;;;;;;;;;;;;;;
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)
    
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)
    
    (expression
     ("(" expression expression ")")
     call-exp)

    ;;;;;;;;;;;;;;;;;; nameless ;;;;;;;;;;;;;;;;;;
    
    (expression
     ("%lexref" number)
     nl-var-exp)
    
    (expression
     ("%let" expression "in" expression)
     nl-let-exp)
    
    (expression
     ("%lexproc" "(" (arbno number) ")" expression )
     nl-proc-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;; nameless environment ;;;;;;;;;;;;;

(define (nl-environment? x)
  ((list-of expval?) x))

(define (empty-nl-env)
  '())

(define (extend-nl-env val env)
  (cons val env))

(define (apply-nl-env env n)
  (list-ref env n))

;;;;;;;;;;;;;;; static environment ;;;;;;;;;;;;;;

(define (empty-senv)
  '())

(define (extend-senv var env)
  (cons var env))

(define (apply-senv env var)
  (cond
    [(null? env)
     (eopl:error 'apply-senv "variable ~s is not bound" var)]
    [(eqv? (car env) var)
     0]
    [else
     (+ 1 (apply-senv (cdr env) var))]))

;;; free variable list -> senv
(define (fv-list->senv ls) ls)

(define (in-senv? env var)
  (cond
    [(null? env) #f]
    [(eqv? (car env) var) #t]
    [else
     (in-senv? (cdr env) var)]))

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
    [diff-exp (exp1 exp2)
              (diff-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [add-exp (exp1 exp2)
             (add-exp (translation-of exp1 senv)
                      (translation-of exp2 senv))]
    [zero?-exp (exp1)
               (zero?-exp (translation-of exp1 senv))]
    [if-exp (exp1 exp2 exp3)
            (if-exp (translation-of exp1 senv)
                    (translation-of exp2 senv)
                    (translation-of exp3 senv))]
    [var-exp (var)
             (nl-var-exp (apply-senv senv var))]
    [let-exp (var exp body)
             (nl-let-exp (translation-of exp senv)
                         (translation-of body
                                         (extend-senv var senv)))]
    [proc-exp (var body)
              (let ([fv-list (get-free-vars body
                                            (extend-senv var
                                                         (empty-senv)))])
                (nl-proc-exp (map-free-vars senv fv-list)
                             (translation-of body
                                             (extend-senv var
                                                          (fv-list->senv fv-list)))))]
    [call-exp (exp1 exp2)
              (call-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [else
     (eopl:error 'translation-of "invalid expression ~A" exp)]))

(define (exists? list x)
  (cond
    [(null? list) #f]
    [(eqv? (car list) x) #t]
    [else
     (exists? (cdr list) x)]))

(define (union ls1 ls2)
  (cond
    [(null? ls1) ls2]
    [(exists? ls2 (car ls1))
     (union (cdr ls1) ls2)]
    [else
     (cons (car ls1)
           (union (cdr ls1) ls2))]))

;; return a senv-to-freevar mapping list
(define (map-free-vars senv fv-list)
  (if (null? fv-list)
      '()
      (cons (apply-senv senv (car fv-list))
            (map-free-vars senv (cdr fv-list)))))

;;; get free variable list
(define (get-free-vars exp senv)
  (cases expression exp
    [const-exp (n)
               '()]
    [var-exp (var)
             (if (in-senv? senv var)
                 '()
                 (list var))]
    [add-exp (exp1 exp2)
             (union (get-free-vars exp1 senv)
                    (get-free-vars exp2 senv))]
    [diff-exp (exp1 exp2)
              (union (get-free-vars exp1 senv)
                     (get-free-vars exp2 senv))]
    [zero?-exp (exp1)
               (get-free-vars exp1 senv)]
    [if-exp (exp1 exp2 exp3)
            (union (get-free-vars exp1 senv)
                   (union (get-free-vars exp2 senv)
                          (get-free-vars exp3 senv)))]
    [let-exp (var exp body)
             (union (get-free-vars exp senv)
                    (get-free-vars body
                                   (extend-senv var senv)))]
    [proc-exp (var body)
              (get-free-vars body (extend-senv var senv))]
    [call-exp (exp1 exp2)
              (union (get-free-vars exp1 senv)
                     (get-free-vars exp2 senv))]
    [else
     (eopl:error 'get-free-vars "invalid expression ~A" exp)]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (body expression?)
   (env nl-environment?)))

(define (apply-procedure p val)
  (cases proc p
    [procedure (body env)
               (value-of body
                         (extend-nl-env val env))]))

;;;;;;;;;;;;;;  expval    ;;;;;;;;;;;;;;

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
    
    [zero?-exp (exp)
               (value-of-arith zero? env exp)]
    
    #|[var-exp (var)
      (apply-env env var)]|#
    [nl-var-exp (num)
                (apply-nl-env env num)]
    [if-exp (exp1 exp2 exp3)
            (if (expval->bool (value-of exp1 env))
                (value-of exp2 env)
                (value-of exp3 env))]
    #|[let-exp (var exp body)
             (value-of body (extend-env var
                                        (value-of exp env)
                                        env))]|#
    [nl-let-exp (exp body)
                (value-of body
                          (extend-nl-env (value-of exp env) env))]
    
    ;;; procedures
    #|[proc-exp (var exp)
              (proc-val (procedure var exp env))]|#
    
    [nl-proc-exp (mapping-list exp)
                 (letrec ([rec (lambda (ls)
                                 (if (null? ls)
                                     (empty-nl-env)
                                     (extend-nl-env (apply-nl-env env (car ls))
                                                    (rec (cdr ls)))))])
                   (proc-val (procedure exp (rec mapping-list))))]
    
    [call-exp (exp1 exp2)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of exp2 env))]
    
    [else
     (eopl:error 'value-of "invalid expression ~A" exp)]))

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