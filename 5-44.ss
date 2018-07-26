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
     ("/" "(" expression "," expression ")")
     div-exp)
    
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
     ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("letcc" identifier "in" expression)
     letcc-exp)

    (expression
     ("call/cc" "(" expression ")")
     callcc-exp)

    (expression
     ("throw" expression "to" expression)
     throw-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;;; exception
    (expression
     ("try" expression "catch" "(" identifier "," identifier ")" expression)
     try-exp)

    (expression
     ("raise" expression)
     raise-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;  continuation  ;;;;;;;;;;;

(define-datatype continuation continuation?
  [end-cont]
  [zero?-cont
   (cont continuation?)]
  [let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?)]
  [if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)]
  [rator-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?)]
  [rand-cont
   (exps (list-of expression?))
   (env environment?)
   (vals (list-of expval?))
   (proc expval?)
   (cont continuation?)]
  [diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [diff2-cont
   (val1 expval?)
   (cont continuation?)]
  [try-cont
   (var1 identifier?)
   (var2 identifier?)
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [raise-cont
   (cont continuation?)]
  [div1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [div2-cont
   (val1 expval?)
   (cont continuation?)]
  [callcc-cont
   (cont continuation?)]
  [throw1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)]
  [throw2-cont
   (val1 expval?)
   (cont continuation?)]
  )

(define (apply-cont cont v)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation. ")
     (print-val v)
     v]
    [zero?-cont (cont1)
                (apply-cont cont1
                            (bool-val (zero? (expval->num v))))]
    [if-test-cont (exp2 exp3 env cont1)
                  (if (expval->bool v)
                      (value-of/k exp2 env cont1)
                      (value-of/k exp3 env cont1))]
    [let-exp-cont (var body env cont1)
                  (value-of/k body
                              (extend-env var v env)
                              cont1)]
    [rator-cont (exps env cont1)
                (if (null? exps)
                    (apply-procedure/k (expval->proc v)
                                       '()
                                       cont1)
                    (value-of/k (car exps) env
                                (rand-cont (cdr exps) env '() v cont1)))]
    [rand-cont (exps env vals val1 cont1)
               (if (null? exps)
                   (apply-procedure/k (expval->proc val1)
                                      (reverse (cons v vals))
                                      cont1)
                   (value-of/k (car exps)
                               env
                               (rand-cont (cdr exps) env
                                          (cons v vals)
                                          val1 cont1)))]
    [diff1-cont (exp2 env cont1)
                (value-of/k exp2 env
                            (diff2-cont v cont1))]
    [diff2-cont (val cont1)
                (apply-cont cont1
                            (num-val (-
                                      (expval->num val)
                                      (expval->num v))))]
    [div1-cont (exp2 env cont1)
               (value-of/k exp2 env
                           (div2-cont v cont1))]
    [div2-cont (val1 cont1)
               (let ([num2 (expval->num v)])
                 (if (zero? num2)
                     (apply-handler val1 cont1)
                     (apply-cont cont1 (num-val (quotient
                                                 (expval->num val1)
                                                 num2)))))]
    [try-cont (var1 var2 exp2 env cont1)
              (apply-cont cont1 v)]
    [raise-cont (cont1)
                (apply-handler v cont1)]
    [callcc-cont (cont1)
                 (apply-procedure/k (expval->proc v)
                                    (list (proc-val (cont-proc cont1)))
                                    cont1)]
    [throw1-cont (exp2 env cont1)
                 (value-of/k exp2 env
                             (throw2-cont v cont1))]
    [throw2-cont (val1 cont1)
                 (apply-procedure/k (expval->proc v)
                                  (list val1)
                                  cont1)]
    ))

(define (apply-handler val cont)
  (let rec ([handler cont])
    (cases continuation handler
      [end-cont ()
                (eopl:error 'apply-handler "uncaught exception ~A" val)]
      [zero?-cont (cont1)
                  (rec cont1)]
      [if-test-cont (exp2 exp3 env cont1)
                    (rec cont1)]
      [let-exp-cont (var body env cont1)
                    (rec cont1)]
      [rator-cont (exp2 env cont1)
                  (rec cont1)]
      [rand-cont (a b c d cont1)
                 (rec cont1)]
      [diff1-cont (exp2 env cont1)
                  (rec cont1)]
      [diff2-cont (val1 cont1)
                  (rec cont1)]
      [div1-cont (exp2 env cont1)
                 (rec cont1)]
      [div2-cont (val1 cont1)
                 (rec cont1)]
      [try-cont (var1 var2 exp2 env cont1)
                (value-of/k exp2
                            (extend-env var2 val
                                        (extend-env var1 (cont-val cont) env))
                            cont1)]
      [raise-cont (cont1)
                  (rec cont1)]
      [callcc-cont (cont1)
                   (rec cont1)]
      [throw1-cont (exp2 env cont1)
                   (rec cont1)]
      [throw2-cont (val1 cont1)
                   (rec cont1)]
      )))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
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
                        (proc-val (procedure bvar body env))
                        (apply-env e svar))]))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?))
  (cont-proc
   (cont continuation?)))

(define (apply-procedure/k p vals cont)
  (cases proc p
    [procedure (vars body env)
               (if (not (= (length vars) (length vals)))
                   (apply-handler (num-val (length vars)) cont)
                   (letrec ([rec (lambda (vars vals e)
                                   (if (null? vars)
                                       e
                                       (rec (cdr vars)
                                         (cdr vals)
                                         (extend-env (car vars)
                                                     (car vals)
                                                     e))))])
                     (value-of/k body
                                 (rec vars vals env)
                                 cont)))]
    [cont-proc (cont1)
               (if (not (= 1 (length vals)))
                   (apply-handler (num-val 1) cont)
                   (apply-cont cont1 (car vals)))]))

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;

(define (print-val v)
  (letrec ([dis (lambda (val need-par)
                  (cases expval val
                    [num-val (num)
                             (display num)]
                    [bool-val (b)
                              (display b)]
                    [proc-val (proc)
                              (display "#procedure")]
                    [null-val ()
                              (display "()")]
                    [pair-val (pair)
                              (when need-par
                                (display "("))
                              (dis (car pair) #t)
                              (cases expval (cdr pair)
                                [null-val ()
                                          (display ")")]
                                [pair-val (pair1)
                                          (display " ")
                                          (dis (cdr pair) #f)]
                                [else
                                 (begin
                                   (display " . ")
                                   (dis (cdr pair) #f)
                                   (display ")"))])]
                    [cont-val (cont)
                              (display "#continuation")]))])
    (dis v #t)
    (newline)))
                
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
  (cont-val
   (cont continuation?)))

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

(define (expval->cont val)
  (cases expval val
    [cont-val (cont) cont]
    [else
     (eopl:error 'expval->cont "expval ~A is not cont" val)]))

(define (expval->pair val)
  (cases expval val
    [pair-val (pair) pair]
    [else
     (eopl:error 'expval->pair "expval ~A is not pair" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (expval-cont? val)
  (cases expval val
    [cont-val (v) #t]
    [else #f]))

;;;;;;;;;;;;;;;;  translator  ;;;;;;;;;;;;;;

(define (translation-of exp)
  (cases expression exp
    [diff-exp (exp1 exp2)
              (diff-exp (translation-of exp1)
                        (translation-of exp2))]
    [div-exp (exp1 exp2)
             (div-exp (translation-of exp1)
                      (translation-of exp2))]
    [zero?-exp (exp1)
               (zero?-exp (translation-of exp1))]
    [if-exp (exp1 exp2 exp3)
            (if-exp (translation-of exp1)
                    (translation-of exp2)
                    (translation-of exp3))]
    [let-exp (var exp1 body)
             (let-exp var
                      (translation-of exp1)
                      (translation-of body))]
    [letrec-exp (p-name b-vars body exp1)
                (letrec-exp p-name b-vars
                            (translation-of body)
                            (translation-of exp1))]
    [proc-exp (vars exp1)
              (proc-exp vars
                        (translation-of exp1))]
    [call-exp (exp1 exp-list)
              (call-exp (translation-of exp1)
                        (map translation-of exp-list))]
    [try-exp (exp1 var1 var2 exp2)
             (try-exp (translation-of exp1)
                      var1 var2
                      (translation-of exp2))]
    [raise-exp (exp1)
               (raise-exp (translation-of exp1))]
    [letcc-exp (var exp1)
               (callcc-exp
                (proc-exp (list var)
                          exp1))]
    [callcc-exp (exp1)
                (callcc-exp (translation-of exp1))]
    [throw-exp (exp1 exp2)
               (call-exp (translation-of exp2)
                         (list (translation-of exp1)))]
    [else
     exp]))

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
      (value-of/k (translation-of exp) (empty-env) (end-cont))]))

(define (value-of/k exp env cont)
  (cases expression exp
    [const-exp (num)
      (apply-cont cont (num-val num))]
    [diff-exp (exp1 exp2)
              (value-of/k exp1 env
                          (diff1-cont exp2 env cont))]
    [div-exp (exp1 exp2)
             (value-of/k exp1 env
                         (div1-cont exp2 env cont))]
    [var-exp (var)
      (apply-cont cont (apply-env env var))]
    [zero?-exp (exp1)
      (value-of/k exp1 env
                  (zero?-cont cont))]
    [if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env
                      (if-test-cont exp2 exp3 env cont))]
    [let-exp (var exp1 body)
             (value-of/k exp1 env
                       (let-exp-cont var body env cont))]
    [letrec-exp (p-name b-vars body exp1)
                (value-of/k exp1 (extend-env-rec p-name b-vars body env) cont)]

    ;;; procedures
    [proc-exp (vars exp1)
              (apply-cont cont (proc-val (procedure vars exp1 env)))]

    [call-exp (exp1 exps)
              (value-of/k exp1 env
                          (rator-cont exps env cont))]

    ;;; exception
    [try-exp (exp1 var1 var2 exp2)
             (value-of/k exp1 env
                         (try-cont var1 var2 exp2 env cont))]
    [raise-exp (exp1)
               (value-of/k exp1 env
                           (raise-cont cont))]

    [letcc-exp (var exp1)
               (value-of/k exp1
                           (extend-env var (cont-val cont) env)
                           cont)]
    [throw-exp (exp1 exp2)
               (value-of/k exp1 env
                           (throw1-cont exp2 env cont))]

    [callcc-exp (exp1)
                (value-of/k exp1 env
                            (callcc-cont cont))]
  ))