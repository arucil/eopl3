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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    (expression
     ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    (expression
     ("set" identifier "=" expression)
     set-exp)

    (expression
     ("begin" expression ";" (arbno expression ";") "end")
     begin-exp)

    (expression
     ("print" "(" (separated-list expression ",") ")")
     print-exp)

    ;;;  list  ;;;;;;;;
    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)
    
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
     ("spawn" "(" expression ")")
     spawn-exp)

    ;;; mutex

    (expression
     ("mutex" "(" ")")
     mutex-exp)

    (expression
     ("wait" "(" expression ")")
     wait-exp)

    (expression
     ("signal" "(" expression ")")
     signal-exp)

    (expression
     ("yield" "(" ")")
     yield-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define continuation? procedure?)

(define (apply-cont cont val)
  (if (time-expired?)
      (begin
        (place-on-ready-queue!
         (cont-thread cont val)
         the-max-time-slice)
        (run-next-thread))
      (begin
        (decrement-timer!)
        (cont val))))

(define (zero?-cont cont)
  (lambda (v)
    (apply-cont cont
                (bool-val (zero? (expval->num v))))))

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

(define (if-test-cont exp2 exp3 env cont)
  (lambda (v)
    (if (expval->bool v)
        (value-of/k exp2 env cont)
        (value-of/k exp3 env cont))))

(define (diff1-cont exp2 env cont)
  (lambda (v)
    (value-of/k exp2 env
                (diff2-cont v cont))))

(define (diff2-cont v1 cont)
  (lambda (v)
    (apply-cont cont
                (num-val (-
                          (expval->num v1)
                          (expval->num v))))))

(define (null?-cont cont)
  (lambda (v)
    (apply-cont cont (bool-val (expval-null? v)))))

(define (cons-car-cont exp2 env cont)
  (lambda (val1)
    (value-of/k exp2 env
                (cons-cdr-cont val1 cont))))

(define (cons-cdr-cont val1 cont)
  (lambda (val2)
    (apply-cont cont (pair-val (cons val1 val2)))))

(define (car-cont cont)
  (lambda (val1)
    (apply-cont cont (car (expval->pair val1)))))

(define (cdr-cont cont)
  (lambda (val1)
    (apply-cont cont (cdr (expval->pair val1)))))

(define (list-cont exps env lst cont)
  (lambda (val1)
    (if (null? exps)
        (letrec ([make-list (lambda (ls val-ls)
                              (if (null? val-ls)
                                  ls
                                  (make-list (pair-val (cons (car val-ls)
                                                             ls))
                                             (cdr val-ls))))])
          (apply-cont cont (make-list (null-val) (cons val1 lst))))
        (value-of/k (car exps) env
                    (list-cont (cdr exps) env
                               (cons val1 lst)
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

(define (set-rhs-cont ref cont)
  (lambda (val)
    (let ([old-val (deref ref)])
      (setref! ref val)
      (apply-cont cont old-val))))

(define (begin-cont exps env cont)
  (lambda (val)
    (if (null? exps)
        (apply-cont cont val)
        (value-of/k (car exps) env
                    (begin-cont (cdr exps) env cont)))))

(define (print-cont exps env cont)
  (lambda (val)
    (letrec ([disp (lambda (v need-par)
                     (cases expval v
                       [bool-val (b)
                                 (display v)]
                       [num-val (n)
                                (display n)]
                       [proc-val (proc)
                                 (display "#procedure")]
                       [null-val ()
                                 (display "()")]
                       [mutex-val (m)
                                  (display "#mutex")]
                       [pair-val (pair)
                                 (when need-par
                                   (display "("))
                                 (disp (car pair) #t)
                                 (cases expval (cdr pair)
                                   [null-val ()
                                             (display ")")]
                                   [pair-val (p)
                                             (display " ")
                                             (disp (cdr pair) #f)]
                                   [else
                                    (begin
                                      (display " . ")
                                      (disp (cdr pair) #f)
                                      (display ")"))])]))])
      (disp val #t)
      (if (null? exps)
          (begin
            (newline)
            (apply-cont cont (num-val 1)))
          (begin
            (display "\t")
            (value-of/k (car exps) env
                        (print-cont (cdr exps) env cont)))))))

(define (end-subthread-cont)
  (lambda (val)
    (run-next-thread)))

(define (end-main-thread-cont)
  (lambda (val)
    (set-final-answer! val)
    (run-next-thread)))

(define (spawn-cont cont)
  (lambda (val)
    (let ([proc1 (expval->proc val)])
      (place-on-ready-queue!
       (new-thread proc1 '() (end-subthread-cont))
       the-max-time-slice)
      (apply-cont cont val))))

(define (wait-cont cont)
  (lambda (val)
    (wait-for-mutex (expval->mutex val)
                    (cont-thread cont (num-val 1)))))

(define (signal-cont cont)
  (lambda (val)
    (signal-mutex (expval->mutex val)
                  (cont-thread cont (num-val 1)))))
                            

;;;;;;;;;;;;;;;;  store   ;;;;;;;;;;;;;;;;

(define the-store 'ha)

(define (empty-store) '())

(define (init-store)
  (set! the-store (empty-store)))

(define reference? integer?)

(define (newref val)
  (let ([len (length the-store)])
    (set! the-store (append the-store (list val)))
    len))

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

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val reference?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-vars (list-of identifier?))
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
                        (newref (proc-val (procedure bvar body env)))
                        (apply-env e svar))]))

;;;;;;;;;;;;;;;;  queue  ;;;;;;;;;;;;;

(define (empty-queue) '())

(define empty? null?)

(define (enqueue queue x)
  (if (empty? queue)
      (list x)
      (cons (car queue)
            (enqueue (cdr queue)
                     x))))

(define (dequeue queue f)
  (f (car queue)
     (cdr queue)))

;;;;;;;;;;;;;;;  thread  ;;;;;;;;;;;;;;;

(define-datatype thread thread?
  (cont-thread
   (cont continuation?)
   (val expval?))
  (new-thread
   (proc proc?)
   (vals (list-of expval?))
   (cont continuation?)))

(define (run-thread th)
  (cases thread th
    [new-thread (proc vals cont)
                (apply-procedure/k proc vals cont)]
    [cont-thread (cont val)
              (apply-cont cont val)]))

(define the-ready-queue 'ha)
(define the-final-answer 'ha)
(define the-max-time-slice 'ha)
(define the-time-remaining 'ha)

(define (init-scheduler! ticks)
  (set! the-ready-queue (empty-queue))
  (set! the-final-answer 'ha)
  (set! the-max-time-slice ticks)
  (set! the-time-remaining the-max-time-slice))

(define (set-final-answer! val)
  (set! the-final-answer val))

(define (time-expired?)
  (zero? the-time-remaining))

(define (decrement-timer!)
  (set! the-time-remaining (- the-time-remaining 1)))

(define (place-on-ready-queue! th time)
  (set! the-ready-queue
        (enqueue the-ready-queue (thread-info th time))))

(define (run-next-thread)
  (if (empty? the-ready-queue)
      the-final-answer
      (dequeue the-ready-queue
               (lambda (ti q)
                 (set! the-ready-queue q)
                 (set! the-time-remaining (get-time ti))
                 (run-thread (get-thread ti))))))

(define (yield-current-thread cont)
  (place-on-ready-queue! (cont-thread cont (num-val 99))
                         the-time-remaining)
  (run-next-thread))

(define thread-info cons)
(define get-thread car)
(define get-time cdr)

;;;;;;;;;;;;;;  mutex  ;;;;;;;;;;;;;;

(define-datatype mutex mutex?
  [a-mutex
   (ref-closed? reference?)
   (ref-wait-queue reference?)])

(define (new-mutex)
  (a-mutex
   (newref #f)
   (newref (empty-queue))))

(define (wait-for-mutex mt th)
  (cases mutex mt
    [a-mutex (closed? queue)
             (if (deref closed?)
                 (begin
                   (setref! queue
                            (enqueue (deref queue) (thread-info th the-time-remaining)))
                   (run-next-thread))
                 (begin
                   (setref! closed? #t)
                   (run-thread th)))]))

(define (signal-mutex m th)
  (cases mutex m
    [a-mutex (closed? queue)
             (when (deref closed?)
               (let ([q (deref queue)])
                 (if (empty? q)
                     (setref! closed? #f)
                     (dequeue q
                              (lambda (ti1 q1)
                                (place-on-ready-queue! (get-thread ti1)
                                                       (get-time ti1))
                                (setref! queue q1))))))
             (run-thread th)]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
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

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (null-val)
  (pair-val
   (pair pair?))
  (mutex-val
   (mutex mutex?)))

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
    [pair-val (cons) cons]
    [else
     (eopl:error 'expval->pair "expval ~A is not pair" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (expval->mutex val)
  (cases expval val
    [mutex-val (m) m]
    [else
     (eopl:error 'expval->mutex "expval ~A is not mutex" val)]))

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define (run ticks prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (init-store)
               (init-scheduler! ticks)
               (value-of/k exp (empty-env) (end-main-thread-cont))]))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (apply-cont cont (num-val num))]
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (diff1-cont exp2 env cont))]
    [var-exp (var)
      (apply-cont cont (deref (apply-env env var)))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (zero?-cont cont))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                      (if-test-cont exp2 exp3 env cont))]
    [let-exp (vars exps body)
             (if (null? vars)
                 (eopl:error 'value-of/k "invalid let expression: ~A" exp)
                 (value-of/k (car exps) env
                             (let-exp-cont vars (cdr exps) env env body cont)))]
    [letrec-exp (p-name b-vars body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-vars body env) cont)]

    ;;; procedures
    [proc-exp (vars exp1)
              (apply-cont cont (proc-val (procedure vars exp1 env)))]

    [call-exp (exp1 exp-list)
              (value-of/k exp1 env
                          (rator-cont exp-list env cont))]

    ;;;;;;; list
    [null-exp ()
              (apply-cont cont (null-val))]
    [null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont))]
    [cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (cons-car-cont exp2 env cont))]
    [car-exp (exp1)
             (value-of/k exp1 env
                         (car-cont cont))]
    [cdr-exp (exp1)
             (value-of/k exp1 env
                         (cdr-cont cont))]

    [list-exp (exps)
              (if (null? exps)
                  (apply-cont cont (null-val))
                  (value-of/k (car exps) env
                              (list-cont (cdr exps) env '() cont)))]

    [begin-exp (exp1 exps)
                   (value-of/k exp1 env
                               (begin-cont exps env cont))]

    [print-exp (exps)
               (if (null? exps)
                   (begin
                     (newline)
                     (apply-cont cont (num-val 1)))
                   (value-of/k (car exps) env
                               (print-cont (cdr exps) env cont)))]

    ;;; set
    [set-exp (var exp1)
             (value-of/k exp1 env
                         (set-rhs-cont (apply-env env var) cont))]

    ;;; spawn
    [spawn-exp (exp1)
               (value-of/k exp1 env
                           (spawn-cont cont))]

    ;; mutex
    [mutex-exp ()
               (apply-cont cont (mutex-val (new-mutex)))]
    [wait-exp (exp1)
              (value-of/k exp1 env
                          (wait-cont cont))]
    [signal-exp (exp1)
                (value-of/k exp1 env
                            (signal-cont cont))]
    [yield-exp ()
               (yield-current-thread cont)]
  ))