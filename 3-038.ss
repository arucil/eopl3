#lang eopl

;;; 3.38

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

    (expression
     ("cond" (arbno expression "==>" expression) "end")
     cond-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("%lexref" number)
     nl-var-exp)

    (expression
     ("%let" expression "in" expression)
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

;;;;;;;;;;;;;;; translator ;;;;;;;;;;;;;;;

(define (translation-of-program prg)
  (cases program prg
    [a-program (exp)
               (a-program
                (translation-of exp (empty-senv)))]))

(define (translation-of-list exp-list senv)
  (if (null? exp-list)
      '()
      (cons (translation-of (car exp-list) senv)
            (translation-of-list (cdr exp-list) senv))))

(define (translation-of exp senv)
  (cases expression exp
    [const-exp (num)
               (const-exp num)]
    [diff-exp (exp1 exp2)
              (diff-exp (translation-of exp1 senv)
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
              (nl-proc-exp (translation-of body
                                            (extend-senv var senv)))]
    [call-exp (exp1 exp2)
              (call-exp (translation-of exp1 senv)
                        (translation-of exp2 senv))]
    [cond-exp (exp-list1 exp-list2)
              (cond-exp (translation-of-list exp-list1 senv)
                        (translation-of-list exp-list2 senv))]
    [else
     (eopl:error 'translation-of "invalid expression ~A" exp)]))
    
;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (body expression?)
   (env nl-environment?)))

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

(define (apply-procedure p val)
  (cases proc p
    [procedure (body env)
               (value-of body
                         (extend-nl-env val env))]))

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
      (num-val (-
                (expval->num (value-of exp1 env))
                (expval->num (value-of exp2 env))))]
    #|[var-exp (var)
      (apply-env env var)]|#
    [nl-var-exp (num)
                (apply-nl-env env num)]
    [zero?-exp (exp)
      (bool-val (zero?
                 (expval->num
                  (value-of exp env))))]
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

    [nl-proc-exp (exp)
                 (proc-val (procedure exp env))]

    [call-exp (exp1 exp2)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of exp2 env))]

    [cond-exp (exp-list1 exp-list2)
              (let loop ([exps1 exp-list1]
                         [exps2 exp-list2])
                (cond
                  [(null? exps1)
                   (eopl:error 'value-of "cond-exp failed")]
                  [(expval->bool (value-of (car exps1) env))
                   (value-of (car exps2) env)]
                  [else
                   (loop (cdr exps1) (cdr exps2))]))]
    
    [else
     (eopl:error 'value-of "invalid expression ~A" exp)]))


(provide run)