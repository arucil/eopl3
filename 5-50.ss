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

(define-datatype continuation continuation?
  [zero?-cont
   (cont continuation?)]
  [let-exp-cont
   (vars (list-of identifier?))
   (exps1 (list-of expression?))
   (env environment?)
   (new-env environment?)
   (body expression?)
   (cont continuation?)]
  [if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [diff2-cont
   (val1 expval?)
   (cont continuation?)]
  [rator-cont
   (exp-list (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [rand-cont
   (p expval?)
   (exps (list-of expression?))
   (vals (list-of expval?))
   (env environment?)
   (cont continuation?)]
  [set-rhs-cont
   (ref reference?)
   (cont continuation?)]
  [begin-cont
    (exps (list-of expression?))
    (env environment?)
    (cont continuation?)]
  [print-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [end-subthread-cont]
  [end-main-thread-cont]
  [spawn-cont
   (cont continuation?)]
  [wait-cont
   (cont continuation?)]
  [signal-cont
   (cont continuation?)]
  )

(define (apply-cont)
  (if (time-expired?)
      (begin
        (place-on-ready-queue!
         (cont-thread cont val))
        (run-next-thread))
      (begin
        (decrement-timer!)
        (cases continuation cont
          [zero?-cont (cont1)
                      (set! cont cont1)
                      (set! val (bool-val (zero? (expval->num val))))
                      (apply-cont)]
          [let-exp-cont (vars exps1 env1 new-env body cont1)
                        (if (null? exps1)
                            (begin
                              (set! exp body)
                              (set! env (extend-env (car vars)
                                                    (newref val)
                                                    new-env))
                              (set! cont cont1)
                              (value-of/k))
                            (begin
                              (set! exp (car exps1))
                              (set! env env1)
                              (set! cont (let-exp-cont (cdr vars)
                                                       (cdr exps1)
                                                       env1
                                                       (extend-env (car vars)
                                                                   (newref val)
                                                                   new-env)
                                                       body
                                                       cont1))
                              (value-of/k)))]
          [if-test-cont (exp2 exp3 env1 cont1)
                        (set! env env1)
                        (set! cont cont1)
                        (set! exp (if (expval->bool val)
                                      exp2
                                      exp3))
                        (value-of/k)]
          [diff1-cont (exp2 env1 cont1)
                      (set! exp exp2)
                      (set! env env1)
                      (set! cont (diff2-cont val cont1))
                      (value-of/k)]
          [diff2-cont (val1 cont1)
                      (set! cont cont1)
                      (set! val (num-val (-
                                            (expval->num val1)
                                            (expval->num val))))
                      (apply-cont)]
          [rator-cont (exp-list env1 cont1)
                      (if (null? exp-list)
                          (begin
                            (set! proc1 (expval->proc val))
                            (set! val '())
                            (set! cont cont1)
                            (apply-procedure/k))
                          (begin
                            (set! exp (car exp-list))
                            (set! env env1)
                            (set! cont (rand-cont val
                                                  (cdr exp-list)
                                                  '()
                                                  env1
                                                  cont1))
                            (value-of/k)))]
          [rand-cont (p exp-list val-list env1 cont1)
                     (if (null? exp-list)
                         (begin
                           (set! proc1 (expval->proc p))
                           (set! val (reverse (cons val val-list)))
                           (set! cont cont1)
                           (apply-procedure/k))
                         (begin
                           (set! exp (car exp-list))
                           (set! env env1)
                           (set! cont (rand-cont p
                                                 (cdr exp-list)
                                                 (cons val val-list)
                                                 env1 cont1))
                           (value-of/k)))]
          [set-rhs-cont (ref cont1)
                        (let ([old-val (deref ref)])
                          (setref! ref val)
                          (set! val old-val)
                          (set! cont cont1)
                          (apply-cont))]
          [begin-cont (exps env1 cont1)
                      (if (null? exps)
                          (begin
                            (set! cont cont1)
                            (apply-cont))
                          (begin
                            (set! exp (car exps))
                            (set! env env1)
                            (set! cont (begin-cont (cdr exps) env1 cont1))
                            (value-of/k)))]
          [print-cont (exps env1 cont1)
                      (letrec ([disp (lambda (v need-par)
                                       (cases expval v
                                         [bool-val (b)
                                                   (display v)]
                                         [num-val (n)
                                                  (display n)]
                                         [proc-val (proc)
                                                   (display "#procedure")]
                                         [mutex-val (m)
                                                    (display "#mutex")]))])
                        (disp val #t)
                        (if (null? exps)
                            (begin
                              (newline)
                              (set! cont cont1)
                              (set! val (num-val 1))
                              (apply-cont))
                            (begin
                              (display "\t")
                              (set! exp (car exps))
                              (set! env env1)
                              (set! cont (print-cont (cdr exps) env1 cont1))
                              (value-of/k))))]
          [end-subthread-cont ()
                              (run-next-thread)]
          [end-main-thread-cont ()
                                (set-final-answer! val)
                                (run-next-thread)]
          [spawn-cont (cont1)
                      (let ([proc1 (expval->proc val)])
                        (place-on-ready-queue!
                         (new-thread proc1 '() (end-subthread-cont)))
                        (set! cont cont1)
                        (apply-cont))]
          [wait-cont (cont1)
                     (set! mutex1 (expval->mutex val))
                     (set! thread1 (cont-thread cont1 (num-val 1)))
                     (wait-for-mutex)]
          [signal-cont (cont1)
                       (set! mutex1 (expval->mutex val))
                       (set! thread1 (cont-thread cont1 (num-val 1)))
                       (signal-mutex)]
          ))))                            

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

(define (run-thread)
  (cases thread thread1
    [new-thread (proc11 vals cont1)
                (set! proc1 proc11)
                (set! val vals)
                (set! cont cont1)
                (apply-procedure/k)]
    [cont-thread (cont1 val1)
                 (set! cont cont1)
                 (set! val val1)
                 (apply-cont)]))

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

(define (place-on-ready-queue! th)
  (set! the-ready-queue
        (enqueue the-ready-queue th)))

(define (run-next-thread)
  (if (empty? the-ready-queue)
      the-final-answer
      (dequeue the-ready-queue
               (lambda (th q)
                 (set! the-ready-queue q)
                 (set! the-time-remaining the-max-time-slice)
                 (set! thread1 th)
                 (run-thread)))))

(define (yield-current-thread)
  (place-on-ready-queue! (cont-thread cont (num-val 99)))
  (run-next-thread))

;;;;;;;;;;;;;;  mutex  ;;;;;;;;;;;;;;

(define-datatype mutex mutex?
  [a-mutex
   (ref-closed? reference?)
   (ref-wait-queue reference?)])

(define (new-mutex)
  (a-mutex
   (newref #f)
   (newref (empty-queue))))

(define (wait-for-mutex)
  (cases mutex mutex1
    [a-mutex (closed? queue)
             (if (deref closed?)
                 (begin
                   (setref! queue
                            (enqueue (deref queue) thread1))
                   (run-next-thread))
                 (begin
                   (setref! closed? #t)
                   (run-thread)))]))

(define (signal-mutex)
  (cases mutex mutex1
    [a-mutex (closed? queue)
             (when (deref closed?)
               (let ([q (deref queue)])
                 (if (empty? q)
                     (setref! closed? #f)
                     (dequeue q
                              (lambda (th1 q1)
                                (place-on-ready-queue! th1)
                                (setref! queue q1))))))
             (run-thread)]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure/k)
  (cases proc proc1
    [procedure (vars body env1)
               (when (not (= (length vars) (length val)))
                 (eopl:error 'apply-procedure/k
                             "argument number mismatch, expects ~A, got ~A"
                             (length vars)
                             (length val)))
               (letrec ([rec (lambda (var-list val-list e)
                               (if (null? var-list)
                                   e
                                   (rec (cdr var-list)
                                     (cdr val-list)
                                     (extend-env (car var-list)
                                                 (newref (car val-list))
                                                 e))))])
                 (set! exp body)
                 (set! env (rec vars val env1))
                 (value-of/k))]))

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
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

(define (expval->mutex val)
  (cases expval val
    [mutex-val (m) m]
    [else
     (eopl:error 'expval->mutex "expval ~A is not mutex" val)]))

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define exp 'ha)
(define env 'ha)
(define cont 'ha)
(define proc1 'ha)
(define val 'ha)
(define mutex1 'ha)
(define thread1 'ha)

(define (run ticks prog)
  (cases program (scan&parse prog)
    [a-program (exp1)
               (init-store)
               (init-scheduler! ticks)
               (set! exp exp1)
               (set! env (empty-env))
               (set! cont (end-main-thread-cont))
               (value-of/k)]))

(define (value-of/k)
  (cases expression exp
    [const-exp (num)
               (set! val (num-val num))
               (apply-cont)]
    [diff-exp (exp1 exp2)
              (set! exp exp1)
              (set! cont (diff1-cont exp2 env cont))
              (value-of/k)]
    [var-exp (var)
             (set! val (deref (apply-env env var)))
             (apply-cont)]
    [zero?-exp (exp1)
               (set! exp exp1)
               (set! cont (zero?-cont cont))
               (value-of/k)]
    [if-exp (exp1 exp2 exp3)
            (set! exp exp1)
            (set! cont (if-test-cont exp2 exp3 env cont))
            (value-of/k)]
    [let-exp (vars exps body)
             (if (null? vars)
                 (eopl:error 'value-of/k "invalid let expression: ~A" exp)
                 (begin
                   (set! exp (car exps))
                   (set! cont (let-exp-cont vars (cdr exps) env env body cont))
                   (value-of/k)))]
    [letrec-exp (p-name b-vars body exp1)
                (set! exp exp1)
                (set! env (extend-env-rec p-name b-vars body env))
                (value-of/k)]

    ;;; procedures
    [proc-exp (vars exp1)
              (set! val (proc-val (procedure vars exp1 env)))
              (apply-cont)]

    [call-exp (exp1 exp-list)
              (set! exp exp1)
              (set! cont (rator-cont exp-list env cont))
              (value-of/k)]

    [begin-exp (exp1 exps)
               (set! exp exp1)
               (set! cont (begin-cont exps env cont))
               (value-of/k)]

    [print-exp (exps)
               (if (null? exps)
                   (begin
                     (newline)
                     (set! val (num-val 1))
                     (apply-cont))
                   (begin
                     (set! exp (car exps))
                     (set! cont (print-cont (cdr exps) env cont))
                     (value-of/k)))]

    ;;; set
    [set-exp (var exp1)
             (set! exp exp1)
             (set! cont (set-rhs-cont (apply-env env var) cont))
             (value-of/k)]

    ;;; spawn
    [spawn-exp (exp1)
               (set! exp exp1)
               (set! cont (spawn-cont cont))
               (value-of/k)]

    ;; mutex
    [mutex-exp ()
               (set! val (mutex-val (new-mutex)))
               (apply-cont)]
    [wait-exp (exp1)
              (set! exp exp1)
              (set! cont (wait-cont cont))
              (value-of/k)]
    [signal-exp (exp1)
                (set! exp exp1)
                (set! cont (signal-cont cont))
                (value-of/k)]
    [yield-exp ()
               (yield-current-thread)]
  ))