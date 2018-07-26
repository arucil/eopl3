#lang eopl

;;; 4.13

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
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;;;;;;;;;;;   explicit reference ;;;;;;;;;

    (expression
     ("newref" "(" expression ")")
     newref-exp)

    (expression
     ("deref" "(" expression ")")
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  store  ;;;;;;;;;;;;;;;;

(define (empty-store) '#())

(define store? vector?)

(define (init-store)
  (empty-store))

(define reference? integer?)

(define (vector-copy! old new copy-len)
  (let loop ([n (- copy-len 1)])
    (unless (negative? n)
      (vector-set! new n
                   (vector-ref old n)))))

(define (newref val store)
  (letrec ([old-len (vector-length store)]
           [new-store (make-vector (+ 1 old-len))])
    (vector-copy! store new-store old-len)
    (vector-set! new-store old-len val)
    (cons old-len new-store)))

(define (deref n store)
  (vector-ref store n))

(define (setref ref val store)
  (let* ([len (vector-length store)]
         [new-store (make-vector len)])
    (vector-copy! store new-store len)
    (vector-set! new-store ref val)
    new-store))

;;;;;;;;;;;;;;;; answer  ;;;;;;;;;;;;;

(define-datatype answer answer?
  (an-answer
   (val expval?)
   (store store?)))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define environment? list?)

(define (empty-env) '())

(define (extend-env var val env)
  (cons (cons var val) env))

(define (extend-env* vars vals env)
  (let loop ([var-list vars]
             [val-list vals])
    (if (null? var-list)
        env
        (extend-env (car var-list)
                    (car val-list)
                    (loop (cdr var-list)
                          (cdr val-list))))))

(define (apply-env env svar)
  (cond
    [(null? env)
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [(eqv? (caar env) svar)
     (cdar env)]
    [else
     (apply-env (cdr env) svar)]))

;;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure p vals store)
  (cases proc p
    [procedure (vars body env)
               (value-of body
                         (extend-env* vars vals env)
                         store)]))

;;;;;;;;;;;;;;; expval ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (ref-val
   (ref reference?)))

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

(define (expval->ref val)
  (cases expval val
    [ref-val (ref) ref]
    [else
     (eopl:error 'expval->ref "expval ~A is not ref" val)]))

;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (value-of exp
                         (empty-env)
                         (init-store))]))

(define (value-of exp env store)
  (cases expression exp
    [const-exp (num)
      (an-answer (num-val num) store)]
    [diff-exp (exp1 exp2)
              (cases answer (value-of exp1 env store)
                [an-answer (val1 store1)
                           (cases answer (value-of exp2 env store1)
                             [an-answer (val2 store2)
                                        (an-answer (num-val (-
                                                             (expval->num val1)
                                                             (expval->num val2)))
                                                   store2)])])]
    [var-exp (var)
             (an-answer
              (apply-env env var)
              store)]
    [zero?-exp (exp1)
               (cases answer (value-of exp1 env store)
                 [an-answer (val1 store1)
                            (an-answer (bool-val (zero? (expval->num val1)))
                                       store1)])]
    [if-exp (exp1 exp2 exp3)
            (cases answer (value-of exp1 env store)
              [an-answer (val1 store1)
                         (if (expval->bool val1)
                             (value-of exp2 env store1)
                             (value-of exp3 env store1))])]
    [let-exp (var exp body)
             (cases answer (value-of exp env store)
               [an-answer (val1 store1)
                          (value-of body
                                    (extend-env var val1 env)
                                    store1)])]

    ;;; procedures
    [proc-exp (var exp)
              (an-answer
               (proc-val (procedure var exp env))
               store)]

    [call-exp (exp1 exp-list)
              (cases answer (value-of exp1 env store)
                [an-answer (val1 store1)
                           (letrec ([new-store store1]
                                    [rec (lambda (ls)
                                           (if (null? ls)
                                               '()
                                               (cases answer (value-of (car ls) env new-store)
                                                 [an-answer (val2 store2)
                                                            (set! new-store store2)
                                                            (cons val2
                                                                  (rec (cdr ls)))])))]
                                    [vals (rec exp-list)])
                             (apply-procedure (expval->proc val1)
                                              vals
                                              new-store))])]
    ;;; reference
    [newref-exp (exp1)
                (cases answer (value-of exp1 env store)
                  [an-answer (val1 store1)
                             (let ([res (newref val1 store1)])
                               (an-answer (ref-val (car res))
                                          (cdr res)))])]
    [deref-exp (exp1)
               (cases answer (value-of exp1 env store)
                 [an-answer (val1 store1)
                            (an-answer (deref (expval->ref val1) store1)
                                       store1)])]
    [setref-exp (exp1 exp2)
                (cases answer (value-of exp1 env store)
                  [an-answer (val1 store1)
                             (cases answer (value-of exp2 env store1)
                               [an-answer (val2 store2)
                                          (let* ([ref (expval->ref val1)]
                                                 [old-val (deref ref store2)])
                                            (an-answer old-val
                                                       (setref ref val2 store2)))])])]
    ))