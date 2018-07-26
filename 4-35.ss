#lang eopl

;; 4.35

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

    (expression
     ("set" identifier "=" expression)
     assign-exp)

    (expression
     ("ref" identifier)
     ref-exp)

    (expression
     ("deref" "(" expression ")")
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)

    (expression
     ("begin" (separated-list expression ";") "end")
     begin-exp)

    (expression
     ("print" "(" expression ")")
     print-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  store  ;;;;;;;;;;;;;;;;

(define the-store 'ha)

(define (empty-store) '())

(define (init-store)
  (set! the-store (empty-store)))

(define reference? integer?)

(define (newref val)
  (let ([len (length the-store)])
    (set! the-store (append the-store (list val)))
    len))

(define (newref* vals)
  (if (null? vals)
      '()
      (cons (newref (car vals))
            (newref* (cdr vals)))))

(define (deref n)
  (list-ref the-store n))

(define (setref! ref val)
  (let ([old-val (deref ref)])
    (set! the-store
          (let loop ([store the-store]
                     [n ref])
            (cond
              [(null? store)
               (eopl:error 'setref! "invalid reference ~A of ~A" ref the-store)]
              [(zero? n)
               (cons val (cdr store))]
              [else
               (cons (car store)
                     (loop (cdr store) (- n 1)))])))
    old-val))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define environment? list?)

(define (empty-env) '())

(define (extend-env var ref env)
  (cons (cons var ref) env))

(define (apply-env env svar)
  (cond
    [(null? env)
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [(eqv? svar (caar env))
     (cdar env)]
    [else
     (apply-env (cdr env) svar)]))

(define (extend-env-rec p-names b-vars p-bodies env)
  (let ([new-env
         (let loop ([ls p-names])
           (if (null? ls)
               env
               (extend-env (car ls)
                           (newref (num-val 1))
                           (loop (cdr ls)))))])
    (let loop ([ls-pname p-names]
               [ls-vars b-vars]
               [ls-body p-bodies])
      (unless (null? ls-pname)
        (setref! (apply-env new-env (car ls-pname))
                 (proc-val (procedure (car ls-vars)
                                      (car ls-body)
                                      new-env)))
        (loop (cdr ls-pname)
              (cdr ls-vars)
              (cdr ls-body))))
    new-env))

;;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (p-vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure p vals)
  (cases proc p
    [procedure (vars body env)
               (when (not (= (length vars) (length vals)))
                 (eopl:error 'apply-procedure "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length vals)))
               (letrec ([rec (lambda (var-list refs)
                               (if (null? var-list)
                                   env
                                   (extend-env (car var-list)
                                               (car refs)
                                               (rec (cdr var-list)
                                                 (cdr refs)))))])
                 (value-of body (rec vars (newref* vals))))]))

;;;;;;;;;;;;;;;; expval  ;;;;;;;;;;;;;;;;;

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
     (eopl:error 'expval->proc "expval ~A is not ref" val)]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (init-store)
               (value-of exp (empty-env))]))

(define (value-of-arith op env . exps)
  (let ([val (apply op (map (lambda (x)
                              (expval->num (value-of x env)))
                            exps))])
    ((cond
      [(number? val) num-val]
      [(boolean? val) bool-val]
      [else
       (eopl:error 'value-of-binary "value ~A is not num or bool" val)])
     val)))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
      (value-of-arith - env exp1 exp2)]
    [var-exp (var)
      (deref (apply-env env var))]
    [zero?-exp (exp)
      (value-of-arith zero? env exp)]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (vars exps body)
             (letrec ([rec (lambda (var-list exp-list)
                             (if (null? var-list)
                                 env
                                 (extend-env (car var-list)
                                             (newref (value-of (car exp-list) env))
                                             (rec (cdr var-list)
                                               (cdr exp-list)))))])
               (value-of body (rec vars exps)))]
    [letrec-exp (p-names b-vars bodies exp)
                (value-of exp (extend-env-rec p-names b-vars bodies env))]

    ;;; procedures
    [proc-exp (var exp)
              (proc-val (procedure var exp env))]

    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]

    [assign-exp (var exp1)
                (setref! (apply-env env var)
                         (value-of exp1 env))]

    [begin-exp (exp-list)
               (let loop ([ls exp-list])
                 (cond
                   [(null? ls)
                    (eopl:error 'value-of "invalid begin exp: ~A" exp)]
                   [(null? (cdr ls))
                    (value-of (car ls) env)]
                   [else
                    (value-of (car ls) env)
                    (loop (cdr ls))]))]

    [print-exp (exp1)
               (letrec ([dis (lambda (v)
                               (cases expval v
                                 [num-val (num)
                                          (display num)]
                                 [bool-val (bool)
                                           (display bool)]
                                 [proc-val (proc)
                                           (display "procedure")]
                                 [ref-val (ref)
                                          (display "&(")
                                          (dis (deref ref))
                                          (display ")")]))])
                 (dis (value-of exp1 env))
                 (newline)
                 (num-val 1))]

    [ref-exp (var)
             (ref-val (apply-env env var))]

    [deref-exp (exp1)
             (deref (expval->ref (value-of exp1 env)))]

    [setref-exp (exp1 exp2)
               (let ([ref (expval->ref (value-of exp1 env))])
                 (setref! ref (value-of exp2 env)))]
    ))