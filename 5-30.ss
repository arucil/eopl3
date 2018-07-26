#lang eopl

;;; 5.30

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
     ("(" expression expression ")")
     call-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)))

(define (apply-procedure/k)
  (cases proc proc1
    [procedure (var body)
               (set! exp body)
               (set! env (extend-env var val env))
               (eopl:printf "evaluating body of proc\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
               (value-of/k)]))

;;;;;;;;;;;;;  expval  ;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;;;

(define-datatype continuation continuation?
  [end-cont]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [diff2-cont
   (val1 expval?)
   (env environment?)
   (cont continuation?)]
  [zero?-cont
   (cont continuation?)]
  [if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)]
  [let-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?)]
  [rator-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [rand-cont
   (val1 expval?)
   (env environment?)
   (cont continuation?)]
  )

(define (apply-cont)
  (cases continuation cont
    [end-cont ()
              (eopl:printf "end of computation. ~A\n" val)]
    [diff1-cont (exp2 env1 cont1)
                (set! cont (diff2-cont val env1 cont1))
                (set! exp exp2)
                (set! env env1)
                (eopl:printf "evaluating second operand of diff\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
                (value-of/k)]
    [diff2-cont (val1 env1 cont1)
                (set! val (num-val (-
                                    (expval->num val1)
                                    (expval->num val))))
                (set! cont cont1)
                (eopl:printf "sending diff result ~A to continuation\nenv =\n~A\ncontinuation =\n~A\n"
                           val env cont)
                (apply-cont)]
    [zero?-cont (cont1)
                (set! val (bool-val (zero? (expval->num val))))
                (set! cont cont1)
                (eopl:printf "sending zero? result to continuation\nenv =\n~A\ncontinuation =\n~A\n"
                           val env cont)
                (apply-cont)]
    [if-test-cont (exp2 exp3 env1 cont1)
                  (set! env env1)
                  (set! cont cont1)
                  (set! exp (if (expval->bool val)
                                exp2
                                exp3))
                  (eopl:printf "evaluating action of if\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
                  (value-of/k)]
    [let-cont (var body env1 cont1)
              (set! cont cont1)
              (set! env (extend-env var val env1))
              (set! exp body)
              (eopl:printf "evaluating body of let\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
              (value-of/k)]
    [rator-cont (exp2 env1 cont1)
                (set! cont (rand-cont val env1 cont1))
                (set! exp exp2)
                (set! env env1)
                (eopl:printf "evaluating operand of call\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
                (value-of/k)]
    [rand-cont (val1 env1 cont1)
               (set! proc1 (expval->proc val1))
               (set! env env1)
               (set! cont cont1)
               (eopl:printf "entering call with ~A\nenv =\n~A\ncontinuation =\n~A\n"
                           val env cont)
               (apply-procedure/k)]
  
              ))

;;;;;;;;;;;;;;;  globals  ;;;;;;;;;;;;;

(define exp 'ha)
(define env 'ha)
(define cont 'ha)
(define val 'ha)
(define proc1 'ha)

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp1)
               (set! exp exp1)
               (set! env (empty-env))
               (set! cont (end-cont))
               (value-of/k)]))

(define (value-of/k)
  (cases expression exp
    [const-exp (num)
               (set! val (num-val num))
               (apply-cont)]
    [diff-exp (exp1 exp2)
              (set! cont (diff1-cont exp2 env cont))
              (set! exp exp1)
              (eopl:printf "evaluating first operand of diff\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
              (value-of/k)]
    [var-exp (var)
             (set! val (apply-env env var))
             (apply-cont)]
    [zero?-exp (exp1)
               (set! exp exp1)
               (set! cont (zero?-cont cont))
               (eopl:printf "evaluating operand of zero?\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
               (value-of/k)]
    [if-exp (exp1 exp2 exp3)
            (set! cont (if-test-cont exp2 exp3 env cont))
            (set! exp exp1)
            (eopl:printf "evaluating condition of if\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
            (value-of/k)]
    [let-exp (var exp1 body)
             (set! cont (let-cont var body env cont))
             (set! exp exp1)
             (eopl:printf "evaluating initializer of let\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
             (value-of/k)]

    ;;; procedures
    [proc-exp (var body)
              (set! val (proc-val (procedure var body)))
              (apply-cont)]

    [call-exp (exp1 exp2)
              (set! cont (rator-cont exp2 env cont))
              (set! exp exp1)
              (eopl:printf "evaluating operator of call\nenv =\n~A\ncontinuation =\n~A\n"
                           env cont)
              (value-of/k)]
    ))