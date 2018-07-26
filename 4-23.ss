#lang eopl

;; 4.23

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
  '((program (statement) a-program)

    (statement
     (identifier "=" expression)
     assign-stm)

    (statement
     ("print" expression)
     print-stm)

    (statement
     ("{" (separated-list statement ";") "}")
     seq-stm)

    (statement
     ("if" expression statement statement)
     if-stm)

    (statement
     ("while" expression statement)
     while-stm)

    (statement
     ("var" (separated-list identifier ",") ";" statement)
     block-stm)

    (statement
     ("read" identifier)
     read-stm)
    

    ;;;;;;;;;;;;;;   expression   ;;;;;;;;;;;;
    
    (expression (number) const-exp)

    (expression
     ("+" "(" expression "," expression ")")
     add-exp)
    
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)

    (expression
     ("/" "(" expression "," expression ")")
     div-exp)

    (expression
     ("not" "(" expression ")")
     not-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
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
     ("begin" (separated-list expression ";") "end")
     begin-exp)
    
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
  (uninit-val)
  (num-val
   (num integer?))
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

(define (expval->inited? val)
  (cases expval val
    [uninit-val () #f]
    [else #t]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (stm)
               (init-store)
               (run-stm stm (empty-env))]))

(define (run-stm stm env)
  (cases statement stm
    [assign-stm (var exp1)
                (setref! (apply-env env var)
                         (value-of exp1 env))]
    [print-stm (exp1)
               (cases expval (value-of exp1 env)
                 [num-val (num)
                          (display num)]
                 [bool-val (bool)
                           (display bool)]
                 [proc-val (proc)
                           (display "procedure")]
                 [else
                  (eopl:error 'run-stm "unreachable ~A" exp1)])
               (newline)]
    [seq-stm (stms)
             (let loop ([ls stms])
               (unless (null? ls)
                 (run-stm (car ls) env)
                 (loop (cdr ls))))]
    [if-stm (exp1 stm1 stm2)
            (if (expval->bool (value-of exp1 env))
                (run-stm stm1 env)
                (run-stm stm2 env))]
    [while-stm (exp1 stm1)
               (let loop ()
                 (when (expval->bool (value-of exp1 env))
                   (run-stm stm1 env)
                   (loop)))]
    [block-stm (vars stm1)
               (letrec ([rec (lambda (ls)
                               (if (null? ls)
                                   env
                                   (extend-env (car ls)
                                               (newref (uninit-val))
                                               (rec (cdr ls)))))])
                 (run-stm stm1 (rec vars)))]
    [read-stm (var)
              (let ([ref (apply-env env var)]
                    [num (read)])
                (if (and (integer? num)
                         (>= num 0))
                    (setref! ref (num-val num))
                    (eopl:error 'run-stm "invalid input ~A" num)))]
    ))

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
    [add-exp (exp1 exp2)
      (value-of-arith + env exp1 exp2)]
    [diff-exp (exp1 exp2)
      (value-of-arith - env exp1 exp2)]
    [mult-exp (exp1 exp2)
      (value-of-arith * env exp1 exp2)]
    [div-exp (exp1 exp2)
      (value-of-arith quotient env exp1 exp2)]
    [var-exp (var)
             (let ([val (deref (apply-env env var))])
               (if (expval->inited? val)
                   val
                   (eopl:error 'value-of "attempt to refer to uninitialized variable ~s" var)))]
    [zero?-exp (exp1)
      (value-of-arith zero? env exp1)]
    [not-exp (exp1)
      (bool-val (not (expval->bool (value-of exp1 env))))]
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
    [proc-exp (vars exp)
              (proc-val (procedure vars exp env))]

    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]

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
    ))