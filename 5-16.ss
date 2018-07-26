#lang eopl

;; 5.16

;; procedural representation of continuations

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

;;;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;;;

(define (end-cont)
  (lambda ()
    (eopl:printf "end of program.\n")))

(define (apply-command-cont cont)
  (cont))

(define (apply-cont cont val)
  (cont val))

(define (binary1-cont op exp2 env cont)
  (lambda (val1)
    (value-of/k exp2 env
                (binary2-cont op val1 cont))))

(define (binary2-cont op val1 cont)
  (lambda (val2)
    (apply-cont cont (num-val (op
                               (expval->num val1)
                               (expval->num val2))))))

(define (zero?-cont cont)
  (lambda (val)
    (apply-cont cont (bool-val (zero? (expval->num val))))))

(define (not-cont cont)
  (lambda (val)
    (apply-cont cont (bool-val (not (expval->bool val))))))

(define (if-exp-cont exp2 exp3 env cont)
  (lambda (val)
    (if (expval->bool val)
        (value-of/k exp2 env cont)
        (value-of/k exp3 env cont))))

(define (let-exp-cont vars exps1 env new-env body cont)
  (lambda (val)
    (if (null? exps1)
        (value-of/k body
                    (extend-env (car vars)
                                (newref val)
                                new-env)
                    cont)
        (value-of/k (car exps1)
                    env
                    (let-exp-cont (cdr vars)
                                  (cdr exps1)
                                  env
                                  (extend-env (car vars)
                                              (newref val)
                                              new-env)
                                  body
                                  cont)))))

(define (rator-cont exp-list env cont)
  (lambda (p)
    (if (null? exp-list)
        (apply-procedure/k (expval->proc p) '() cont)
        (value-of/k (car exp-list) env
                    (rand-cont p
                               (cdr exp-list)
                               '()
                               env
                               cont)))))

(define (rand-cont p exp-list val-list env cont)
  (lambda (v)
    (if (null? exp-list)
        (apply-procedure/k (expval->proc p)
                           (reverse (cons v val-list))
                           cont)
        (value-of/k (car exp-list) env
                    (rand-cont p
                               (cdr exp-list)
                               (cons v val-list)
                               env
                               cont)))))

(define (begin-cont exps env cont)
  (lambda (val)
    (if (null? exps)
        (apply-cont cont val)
        (value-of/k (car exps) env
                    (begin-cont (cdr exps) env cont)))))

(define (assign-cont ref cont)
  (lambda (val)
    (setref! ref val)
    (apply-command-cont cont)))

(define (print-cont cont)
  (lambda (val)
    (cases expval val
      [num-val (num)
               (display num)]
      [bool-val (bool)
                (display bool)]
      [proc-val (proc)
                (display "procedure")]
      [else
       (eopl:error 'print-cont "unreachable")])
    (newline)
    (apply-command-cont cont)))

(define (seq-cont stms env cont)
  (lambda ()
    (if (null? stms)
        (apply-command-cont cont)
        (result-of/k (car stms) env
                     (seq-cont (cdr stms) env cont)))))

(define (if-stm-cont stm1 stm2 env cont)
  (lambda (val)
    (if (expval->bool val)
        (result-of/k stm1 env cont)
        (result-of/k stm2 env cont))))

(define (while-test-cont exp1 stm1 env cont)
  (lambda (val)
    (if (expval->bool val)
        (result-of/k stm1 env
                     (while-body-cont exp1 stm1 env cont))
        (apply-command-cont cont))))

(define (while-body-cont exp1 stm1 env cont)
  (lambda ()
    (value-of/k exp1 env
                (while-test-cont exp1 stm1 env cont))))

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

(define (apply-procedure/k p vals cont)
  (cases proc p
    [procedure (vars body env)
               (when (not (= (length vars) (length vals)))
                 (eopl:error 'apply-procedure/k
                             "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length vals)))
               (letrec ([rec (lambda (var-list val-list e)
                               (if (null? var-list)
                                   e
                                   (rec (cdr var-list)
                                     (cdr val-list)
                                     (extend-env (car var-list)
                                                 (newref (car val-list))
                                                 e))))])
                 (value-of/k body (rec vars vals env) cont))]))

;;;;;;;;;;;;;;;; expval  ;;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (uninit-val)
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

(define (expval->inited? val)
  (cases expval val
    [uninit-val () #f]
    [else #t]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (stm)
               (init-store)
               (result-of/k stm (empty-env) (end-cont))]))

(define (result-of/k stm env cont)
  (cases statement stm
    [assign-stm (var exp1)
                (value-of/k exp1 env
                            (assign-cont (apply-env env var) cont))]
    [print-stm (exp1)
               (value-of/k exp1 env
                           (print-cont cont))]
    [seq-stm (stms)
             (if (null? stms)
                 (apply-command-cont cont)
                 (result-of/k (car stms) env
                              (seq-cont (cdr stms) env cont)))]
    [if-stm (exp1 stm1 stm2)
            (value-of/k exp1 env
                        (if-stm-cont stm1 stm2 env cont))]
    [while-stm (exp1 stm1)
               (value-of/k exp1 env
                           (while-test-cont exp1 stm1 env cont))]
    [block-stm (vars stm1)
               (letrec ([rec (lambda (ls)
                               (if (null? ls)
                                   env
                                   (extend-env (car ls)
                                               (newref (uninit-val))
                                               (rec (cdr ls)))))])
                 (result-of/k stm1 (rec vars) cont))]
    ))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (apply-cont cont (num-val num))]
    
    [add-exp (exp1 exp2)
             (value-of/k exp1 env
                         (binary1-cont + exp2 env cont))]
    
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (binary1-cont - exp2 env cont))]
    
    [mult-exp (exp1 exp2)
              (value-of/k exp1 env
                          (binary1-cont * exp2 env cont))]
    
    [div-exp (exp1 exp2)
             (value-of/k exp1 env
                         (binary1-cont quotient exp2 env cont))]
    
    [var-exp (var)
             (let ([val (deref (apply-env env var))])
               (if (expval->inited? val)
                   (apply-cont cont val)
                   (eopl:error 'value-of "attempt to refer to uninitialized variable ~s" var)))]
    
    [zero?-exp (exp1)
               (value-of/k exp1 env
                           (zero?-cont cont))]
    
    [not-exp (exp1)
             (value-of/k exp1 env
                         (not-cont cont))]

    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                        (if-exp-cont exp2 exp3 env cont))]
    
    [let-exp (vars exps body)
             (if (null? vars)
                 (eopl:error 'value-of/k "invalid let expression: ~A" exp)
                 (value-of/k (car exps) env
                             (let-exp-cont vars (cdr exps) env env body cont)))]
    
    [letrec-exp (p-names b-vars bodies exp1)
                (value-of/k exp1 (extend-env-rec p-names b-vars bodies env) cont)]

    ;;; procedures
    [proc-exp (vars body)
              (apply-cont cont (proc-val (procedure vars body env)))]

    [call-exp (exp1 exps)
              (value-of/k exp1 env
                          (rator-cont exps env cont))]

    [begin-exp (exps)
               (if (null? exps)
                   (eopl:error 'value-of/k "invalid begin expression: ~A" exp)
                   (value-of/k (car exps) env
                               (begin-cont (cdr exps) env cont)))]
    ))

(run "
var f, j; {
  f = proc(n)
        letrec fib(a,b,i) =
                 if zero?(-(n, i))
                 then b
                 else let c = +(a, b)
                          d = b
                      in (fib d c +(i, 1))
        in (fib 1 1 1);
  j = 1;
  while not(zero?(-(j, 16))) {
    print (f j);
    j = +(j, 1)
  }
}")