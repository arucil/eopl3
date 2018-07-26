#lang eopl

;; 4.27

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
     ("do" statement "while" expression)
     do-while-stm)

    (statement
     ("var" (separated-list identifier "=" expression ",") ";" statement)
     block-stm)

    (statement
     ("read" identifier)
     read-stm)

    (statement
     ("call" expression (arbno "," expression))
     call-stm)
    

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

    ;;;;   add leading { and trailing } to avoid grammar conflict
    (expression
     ("sub" "(" (separated-list identifier ",") ")" "{" (separated-list statement ";") "}")
     sub-exp)

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

(define (callable-exp? exp)
  (cases expression exp
    [proc-exp (a c) #t]
    [sub-exp (a c) #t]
    [else #f]))

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
                 (proc-val (callable (car ls-vars)
                                     (car ls-body)
                                     new-env)))
        (loop (cdr ls-pname)
              (cdr ls-vars)
              (cdr ls-body))))
    new-env))

;;;;;;;;;;;;;;;  procedure & subroutine ;;;;;;;;;;;;;;;;;;;

(define-datatype calla calla?
  (callable
   (p-vars (list-of identifier?))
   (body (lambda (x)
           (or
            (expression? x)
            ((list-of statement?) x))))
   (env environment?)))

(define (apply-callable p vals)
  (cases calla p
    [callable (vars body env)
               (when (not (= (length vars) (length vals)))
                 (eopl:error 'apply-procedure "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length vals)))
               (letrec ([new-env (let loop ([var-list vars]
                                            [refs (newref* vals)]
                                            [e env])
                                   (if (null? var-list)
                                       e
                                       (loop (cdr var-list)
                                             (cdr refs)
                                             (extend-env (car var-list)
                                                         (car refs)
                                                         e))))])
                 (if (expression? body)
                     (value-of body new-env)
                     (let loop ([ls body])
                       (unless (null? ls)
                         (run-stm (car ls) new-env)
                         (loop (cdr ls))))))]))

;;;;;;;;;;;;;;;; expval  ;;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num integer?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc calla?))
  (sub-val
   (sub calla?)))

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

(define (expval->sub val)
  (cases expval val
    [sub-val (sub) sub]
    [else
     (eopl:error 'expval->sub "expval ~A is not sub" val)]))

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
                 [sub-val (sub)
                          (display "subroutine")])
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
    [do-while-stm (stm1 exp1)
                  (let loop ()
                    (run-stm stm1 env)
                    (when (expval->bool (value-of exp1 env))
                      (loop)))]
    [block-stm (vars exps stm1)
               (letrec ([proc-list '()]
                        [new-env (let loop ([var-list vars]
                                            [exp-list exps]
                                            [e env])
                                   (if (null? var-list)
                                       e
                                       (loop (cdr var-list)
                                         (cdr exp-list)
                                         (extend-env (car var-list)
                                                     (if (callable-exp? (car exp-list))
                                                         (let ([ref (newref (num-val 1))])
                                                           (set! proc-list (cons
                                                                            (cons ref (car exp-list))
                                                                            proc-list))
                                                           ref)
                                                         (newref (value-of (car exp-list) env)))
                                                     e))))]
                        [fix-proc (lambda (ls)
                               (unless (null? ls)
                                 (cases expression (cdar ls)
                                   [proc-exp (vars body)
                                             (setref! (caar ls)
                                                      (proc-val (callable vars body new-env)))]
                                   [sub-exp (vars body)
                                            (setref! (caar ls)
                                                     (sub-val (callable vars body new-env)))]
                                   [else
                                    (eopl:error 'run-stm "unreachable ~A" ls)])
                                 (fix-proc (cdr ls))))])
                 (fix-proc proc-list)
                 (run-stm stm1 new-env))]
    [read-stm (var)
              (let ([ref (apply-env env var)]
                    [num (read)])
                (if (and (integer? num)
                         (>= num 0))
                    (setref! ref (num-val num))
                    (eopl:error 'run-stm "invalid input ~A" num)))]
    [call-stm (exp1 exps)
              (apply-callable (expval->sub (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]
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
             (deref (apply-env env var))]
    [zero?-exp (exp1)
      (value-of-arith zero? env exp1)]
    [not-exp (exp1)
      (bool-val (not (expval->bool (value-of exp1 env))))]
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
    [proc-exp (vars body)
              (proc-val (callable vars body env))]
    [sub-exp (vars stms)
              (sub-val (callable vars stms env))]

    [call-exp (exp1 exps)
              (apply-callable (expval->proc (value-of exp1 env))
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