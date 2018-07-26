#lang eopl

;; send(id, expr)     sending message to another thread
;; recv()             receiving message from another thread, blocking if no message

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

    (expression
     ("parent" "(" ")")
     parent-exp)

    (expression
     ("kill" "(" expression ")")
     kill-exp)

    (expression
     ("send" "(" expression "," expression ")")
     send-exp)

    (expression
     ("recv" "(" ")")
     recv-exp)
    
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
         (cont-thread cont val (get-thread-id) (get-thread-parent-id))
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
                                 (display b)]
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
    (let* ([proc1 (expval->proc val)]
          [new-id (new-thread-id)]
          [id-val (num-val new-id)])
      (place-on-ready-queue!
       (new-thread proc1 (list id-val)
                   (end-subthread-cont)
                   new-id
                   (get-thread-id))
       the-max-time-slice)
      (apply-cont cont id-val))))

(define (wait-cont cont)
  (lambda (val)
    (wait-for-mutex (expval->mutex val)
                    (cont-thread cont (num-val 1) (get-thread-id) (get-thread-parent-id)))))

(define (signal-cont cont)
  (lambda (val)
    (signal-mutex (expval->mutex val)
                  (cont-thread cont (num-val 1) (get-thread-id) (get-thread-parent-id)))))

(define (kill-cont env cont)
  (lambda (val)
    (let* ([id (expval->num val)]
          [found #f]
          [kill-f (lambda (ti)
                    (if (= id (thread->id (get-thread ti)))
                         (begin
                           (set! found #t)
                           #f)
                         #t))])
      (when (main-thread? id)
        (eopl:error 'kill-cont "cannot kill main thread"))
      (filter-ready-queue kill-f)
      (filter-blocking-queue kill-f)
      (foreach-env env
                   (lambda (var val)
                     (when (expval-mutex? val)
                       (filter-mutex-queue (expval->mutex val) kill-f))))
      (apply-cont cont (bool-val found)))))

(define (send1-cont exp2 env cont)
  (lambda (val)
    (let ([id (expval->num val)])
      (value-of/k exp2 env
                  (send2-cont id cont)))))

(define (send2-cont id cont)
  (lambda (val)
    (send-message! id val cont)))
                            

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

(define (foreach-env env f)
  (cases environment env
    [empty-env () '()]
    [extend-env (var val senv)
                (f var (deref val))
                (foreach-env senv f)]
    ;; ignoring letrec
    [extend-env-rec (a b c senv)
                    (foreach-env senv f)]))

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

(define (filter-queue queue f)
  (cond
    [(null? queue) '()]
    [(f (car queue))
     (cons (car queue)
           (filter-queue (cdr queue) f))]
    [else
     (filter-queue (cdr queue) f)]))

;;;;;;;;;;;;;;;  thread  ;;;;;;;;;;;;;;;

(define-datatype thread thread?
  (cont-thread
   (cont continuation?)
   (val expval?)
   (id integer?)
   (pid integer?))
  (new-thread
   (proc proc?)
   (vals (list-of expval?))
   (cont continuation?)
   (id integer?)
   (pid integer?)))

(define (thread->id th)
  (cases thread th
    [cont-thread (c v i p)
                 i]
    [new-thread (pr v c i p)
                i]))

(define (run-thread th)
  (cases thread th
    [new-thread (proc vals cont id pid)
                (set! current-thread-id id)
                (set! thread-parent-id pid)
                (apply-procedure/k proc vals cont)]
    [cont-thread (cont val id pid)
                 (set! current-thread-id id)
                 (set! thread-parent-id pid)
                 (apply-cont cont val)]))

(define the-ready-queue 'ha)
(define the-final-answer 'ha)
(define the-max-time-slice 'ha)
(define the-time-remaining 'ha)

(define the-thread-id-counter 'ha)
(define current-thread-id 'ha)
(define thread-parent-id 'ha)
(define main-thread-id 'ha)

(define (new-thread-id)
  (set! the-thread-id-counter
        (+ 1 the-thread-id-counter))
  the-thread-id-counter)

(define (get-thread-id)
  current-thread-id)

(define (get-thread-parent-id)
  thread-parent-id)

(define (init-scheduler! ticks)
  (set! the-ready-queue (empty-queue))
  (set! the-final-answer 'ha)
  (set! the-max-time-slice ticks)
  (set! the-time-remaining the-max-time-slice)
  (set! the-thread-id-counter 0)
  (set! thread-parent-id 0)
  (set! current-thread-id (new-thread-id))
  (set! main-thread-id current-thread-id))

(define (main-thread? id)
  (= id main-thread-id))

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

(define (filter-ready-queue f)
  (set! the-ready-queue (filter-queue the-ready-queue f)))

(define (yield-current-thread cont)
  (place-on-ready-queue! (cont-thread cont (num-val 99)
                                      (get-thread-id)
                                      (get-thread-parent-id))
                         the-time-remaining)
  (run-next-thread))

(define thread-info cons)
(define get-thread car)
(define get-time cdr)

;;;;;;;;;;;;;  message queue  ;;;;;;;;;;;;

(define the-message-queue 'ha)
(define the-blocking-queue 'ha)

(define (init-message)
  (set! the-message-queue (empty-queue))
  (set! the-blocking-queue (empty-queue)))

(define (message-id msg)
  (car msg))

(define (message-val msg)
  (cdr msg))

(define (new-message id val)
  (cons id val))

(define (filter-blocking-queue f)
  (set! the-blocking-queue
        (filter-queue the-blocking-queue f)))

(define (recv-message! cont)
  (let ([recvd '()])
    (set! the-message-queue
          (filter-queue the-message-queue
                        (lambda (msg)
                          (if (and (null? recvd)
                                   (= (message-id msg)
                                      (get-thread-id)))
                              (begin
                                (set! recvd (message-val msg))
                                #f)
                              #t))))
    (if (null? recvd)
        (begin
          (set! the-blocking-queue
                (enqueue the-blocking-queue
                         (thread-info
                          (cont-thread cont
                                       (null-val)
                                       (get-thread-id)
                                       (get-thread-parent-id))
                          the-time-remaining)))
          (run-next-thread))
        (apply-cont cont recvd))))

(define (send-message! send-id val cont)
  (let ([sent #f])
    (filter-blocking-queue
     (lambda (ti)
       (cases thread (get-thread ti)
         [cont-thread (cont1 val1 id pid)
                          (if (and (not sent)
                                   (= id
                                      send-id))
                              (begin
                                (set! sent #t)
                                (place-on-ready-queue!
                                 (cont-thread cont1 val id pid)
                                 (get-time ti))
                                #f)
                              #t)]
         [else
          (eopl:error 'send-message! "unreachable ~A" ti)])))
    (when (not sent)
      (set! the-message-queue
            (enqueue the-message-queue
                     (new-message send-id val))))
    (apply-cont cont (bool-val sent))))
                                                 

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

(define (filter-mutex-queue m f)
  (cases mutex m
    [a-mutex (closed? queue)
             (setref! queue (filter-queue (deref queue) f))]))

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

(define (expval-mutex? val)
  (cases expval val
    [mutex-val (m) #t]
    [else #f]))

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define (run ticks prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (init-store)
               (init-scheduler! ticks)
               (init-message)
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

    [parent-exp ()
                (apply-cont cont (num-val (get-thread-parent-id)))]

    [kill-exp (exp1)
              (value-of/k exp1 env
                          (kill-cont env cont))]

    [send-exp (exp1 exp2)
              (value-of/k exp1 env
                          (send1-cont exp2 env cont))]
    [recv-exp ()
              (recv-message! cont)]
  ))