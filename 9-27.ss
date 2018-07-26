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
     ("+" "(" expression "," expression ")")
     plus-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("equal?" "(" expression "," expression ")")
     equal?-exp)
    
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
     ("begin" expression ";" (arbno expression ";") "end")
     begin-exp)

    (expression
     ("print" "(" expression ")")
     print-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    (expression
     ("null")
     null-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("self")
     self-exp)

    (expression
     ("object" (arbno identifier "=" expression) "end")
     object-exp)

    (expression
     ("getmethod" "(" expression "," identifier ")")
     getmethod-exp)

    (expression
     ("getfield" "(" expression "," identifier ")")
     getfield-exp)

    (expression
     ("setfield" expression identifier "=" expression)
     setfield-exp)
    
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
   (ref reference?)
   (env environment?))
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (bodies (list-of expression?))
   (env environment?)))

(define (extend-env* vars refs env)
  (if (null? vars)
      env
      (extend-env* (cdr vars)
                   (cdr refs)
                   (extend-env (car vars)
                               (car refs)
                               env))))

(define (location sym list)
  (let loop ([ls list]
             [n 0])
    (cond
      [(null? ls) #f]
      [(eqv? sym (car ls)) n]
      [else
       (loop (cdr ls) (+ n 1))])))

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var ref env)
                (if (eqv? var svar)
                    ref
                    (apply-env env svar))]
    [extend-env-rec (pnames bvarss bodies e)
                    (let ([n (location svar pnames)])
                      (if n
                          (newref
                           (proc-val (procedure
                                      (list-ref bvarss n)
                                      (list-ref bodies n)
                                      env)))
                          (apply-env e svar)))]
    ))

;;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (b-vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure p refs)
  (cases proc p
    [procedure (vars body env)
               (unless (= (length vars)
                          (length refs))
                 (eopl:error 'apply-procedure
                             "argument number mismatch, expecting ~A, got ~A"
                             (length vars)
                             (length refs)))
               (value-of body
                         (extend-env* vars refs env))]))

;;;;;;;;;;;;;;;; expval  ;;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (pair-val
   (pair pair?))
  (null-val)
  (obj-val
   (env environment?)))

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
    [pair-val (proc) proc]
    [else
     (eopl:error 'expval->proc "expval ~A is not pair" val)]))

(define (expval->object val)
  (cases expval val
    [obj-val (proc) proc]
    [else
     (eopl:error 'expval->object "expval ~A is not object" val)]))


(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (expval-pair? val)
  (cases expval val
    [pair-val (v) #t]
    [else #f]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (exp)
               (init-store)
               (value-of exp (empty-env))]))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
      (num-val (- (expval->num (value-of exp1 env))
                  (expval->num (value-of exp2 env))))]
    [plus-exp (exp1 exp2)
      (num-val (+ (expval->num (value-of exp1 env))
                  (expval->num (value-of exp2 env))))]
    [equal?-exp (exp1 exp2)
      (bool-val (= (expval->num (value-of exp1 env))
                   (expval->num (value-of exp2 env))))]
    [var-exp (var)
      (deref (apply-env env var))]
    [zero?-exp (exp1)
      (bool-val (zero? (expval->num (value-of exp1 env))))]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (vars exps body)
             (value-of body (extend-env* vars
                                        (map newref (values-of-exps exps env))
                                        env))]
    [letrec-exp (p-names b-varss bodies exp)
                (value-of exp (extend-env-rec p-names b-varss bodies env))]

    ;;; procedures
    [proc-exp (vars exp)
              (proc-val (procedure vars exp env))]

    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map newref (values-of-exps exps env)))]

    [assign-exp (var exp1)
                (setref! (apply-env env var)
                         (value-of exp1 env))]

    [begin-exp (exp1 exps)
               (let loop ([val (value-of exp1 env)]
                          [exps exps])
                 (if (null? exps)
                     val
                     (loop (value-of (car exps) env)
                           (cdr exps))))]

    [print-exp (exp1)
               (let rec ([val (value-of exp1 env)]
                         [need-par #t])
                 (cases expval val
                   [num-val (num)
                            (display num)]
                   [bool-val (bool)
                             (display bool)]
                   [proc-val (proc)
                             (display "#procedure")]
                   [null-val ()
                             (display "()")]
                   [pair-val (p)
                             (when need-par
                               (display "("))
                             (rec (car p) #t)
                             (cond
                               [(expval-null? (cdr p))
                                (display ")")]
                               [(expval-pair? (cdr p))
                                (display " ")
                                (rec (cdr p) #f)]
                               [else
                                (display " . ")
                                (rec (cdr p) #f)
                                (display ")")])]
                   [obj-val (o)
                            (display "#object")]
                   ))
               (newline)
               (num-val 1)]
    [null-exp ()
              (null-val)]
    [null?-exp (exp1)
               (bool-val (expval-null? (value-of exp1 env)))]
    [car-exp (exp1)
             (car (expval->pair (value-of exp1 env)))]
    [cdr-exp (exp1)
             (cdr (expval->pair (value-of exp1 env)))]
    [cons-exp (exp1 exp2)
              (pair-val (cons (value-of exp1 env)
                              (value-of exp2 env)))]
    [list-exp (exps)
              (make-list (values-of-exps exps env))]

    [self-exp ()
              (deref (apply-env env '%self))]
    [object-exp (vars exps)
                (obj-val (extend-env* vars
                                      (map newref (values-of-exps exps env))
                                      (empty-env)))]
    [getmethod-exp (exp1 m-name)
                   (let* ([o-val (value-of exp1 env)]
                          [o-env (expval->object o-val)]
                          [val (deref (apply-env o-env m-name))])
                     (cases expval val
                       [proc-val (proc1)
                                 (cases proc proc1
                                   [procedure (bvars body env)
                                              (proc-val (procedure bvars body
                                                                   (extend-env
                                                                    '%self
                                                                    (newref o-val)
                                                                    o-env)))])]
                       [else
                        (eopl:error 'value-of
                                    "field ~A is ~A rather than proc"
                                    m-name val)]))]
    [getfield-exp (exp1 f-name)
                  (deref (apply-env
                          (expval->object
                           (value-of exp1 env))
                          f-name))]
    [setfield-exp (exp1 f-name exp2)
                  (setref! (apply-env
                            (expval->object
                             (value-of exp1 env))
                            f-name)
                           (value-of exp2 env))]
    ))

(define (make-list vals)
  (if (null? vals)
      (null-val)
      (pair-val (cons (car vals)
                      (make-list (cdr vals))))))

(define (values-of-exps exps env)
  (if (null? exps)
      '()
      (cons (value-of (car exps) env)
            (values-of-exps (cdr exps) env))))

;;;;;;;;;;;; ;;;;;;;;;;;;;  test ;;;;;;;;;;;;;;;;;;;;

(define (to-expval a)
  (cond
    [(pair? a)
     (pair-val
      (cons (to-expval (car a))
            (to-expval (cdr a))))]
    [(null? a)
     (null-val)]
    [(number? a)
     (num-val a)]
    [(boolean? a)
     (bool-val a)]))

(define (test val prg)
  (let ([val0 (to-expval val)]
        [val1 (run prg)])
    (unless (equal? val0 val1)
      (eopl:error 'test
                  "test failed, ~A != ~A"
                  val0 val1))))

(test '(1 0 0 1)
      "
let make-oddeven
 = proc()
    object
     even = proc(n)
             if zero?(n) then 1
             else (getmethod(self,odd) -(n,1))
     odd = proc(n)
            if zero?(n) then 0
            else (getmethod(self,even) -(n,1))
    end
in let o = (make-oddeven)
in
list((getmethod(o,odd) 13),
     (getmethod(o,odd) 14),
     (getmethod(o,even) 15),
     (getmethod(o,even) 16))
")

(test '((10 20)
        (11 33)
        100
        (11 33)
        (210 33))
      "
let x = 1
in let make-obj =
     proc (x1, y1)
      object
       x = x1
       y = y1
       setx = proc(v) set x = v
       get = proc() list(x, y)
      end
in let o = (make-obj 10 20)
in let v1 = (getmethod(o,get))
       v2 = 0
       v3 = 0
       v4 = 0
in
begin
 setfield o y = 33;
 (getmethod(o,setx) 11);
 set v2 = (getmethod(o,get));
 (getfield(o,setx) 100);  % modify x (= 1) in let rather than o's field x
 set v3 = (getmethod(o,get));
 setfield o setx = proc(v)
                    set x = +(v, 10);  % modify method
 (getmethod(o,setx) 200);
 set v4 = (getmethod(o,get));
 list(v1, v2, x, v3, v4);
end")
