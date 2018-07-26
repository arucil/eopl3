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
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("letrec" optional-type identifier "(" identifier ":" optional-type ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" identifier ":" optional-type ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (optional-type
     ("?")
     no-type)

    (optional-type
     (type)
     a-type)

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" type "->" type ")")
     proc-type)

    (type
     ("%tvar-type" number)
     tvar-type)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-var identifier?)
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

;;;;;;;;;;;;;;;  type environment ;;;;;;;;;;

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv
   (var identifier?)
   (ty type?)
   (tenv tenvironment?)))

(define (apply-tenv tenv svar)
  (cases tenvironment tenv
    [empty-tenv ()
     (eopl:error 'apply-tenv "variable ~s is not bound" svar)]
    [extend-tenv (var ty env)
                (if (eqv? var svar)
                    ty
                    (apply-tenv env svar))]))

;;;;;;;;;;;;;;;;;;  proc  ;;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (env environment?)))

(define (apply-procedure p val)
  (cases proc p
    [procedure (var body env)
               (value-of body
                         (extend-env var val env))]))

;;;;;;;;;;;;;;;;;  expval  ;;;;;;;;;;;;;;;;;;;;;

(define-datatype expval expval?
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

;;;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;;;

(define (run prog)
  (let ([prg (scan&parse prog)])
    (type-of-program prg)
    (cases program prg
      [a-program (exp)
                 (value-of exp (empty-env))])))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
               (num-val num)]
    [diff-exp (exp1 exp2)
              (num-val (- (expval->num (value-of exp1 env))
                          (expval->num (value-of exp2 env))))]
    [var-exp (var)
             (apply-env env var)]
    [zero?-exp (exp1)
               (bool-val (zero? (expval->num (value-of exp1 env))))]
    [if-exp (exp1 exp2 exp3)
            (if (expval->bool (value-of exp1 env))
                (value-of exp2 env)
                (value-of exp3 env))]
    [let-exp (var exp body)
             (value-of body
                       (extend-env var
                                   (value-of exp env)
                                   env))]
    [letrec-exp (ret-ty p-name b-var arg-ty body exp1)
                (value-of exp1 (extend-env-rec p-name b-var body env))]
    
    ;;; procedures
    [proc-exp (var arg-type exp1)
              (proc-val (procedure var exp1 env))]
    
    [call-exp (exp1 exp2)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of exp2 env))]))

;;;;;;;;;;;;;  subst  ;;;;;;;;;;;;;;;;;

(define (apply-one-subst ty0 tvar ty1)
  (cases type ty0
    [proc-type (t0 t1)
               (proc-type (apply-one-subst t0 tvar ty1)
                          (apply-one-subst t1 tvar ty1))]
    [tvar-type (sn)
               (if (equal? ty0 tvar) ty1 ty0)]
    [else ty0]))

(define (apply-subst-to-type ty subst)
  (cases type ty
    [proc-type (t0 t1)
               (proc-type (apply-subst-to-type t0 subst)
                          (apply-subst-to-type t1 subst))]
    [tvar-type (sn)
               (let ([tmp (assoc ty subst)])
                 (if tmp
                     (cdr tmp)
                     ty))]
    [else ty]))

(define (empty-subst) '())

(define (extend-subst subst tvar ty)
  (cons (cons tvar ty)
        (map (lambda (x)
               (cons (car x)
                     (apply-one-subst (cdr x) tvar ty)))
             subst)))

(define substitution? (list-of pair?))

;;;;;;;;;;;;;;;  equation list ;;;;;;;;;;;;;

(define-datatype eq-list eq-list?
  (empty-eq-list)
  (extend-eq-list
   (eql eq-list?)
   (ty1 type?)
   (ty2 type?)
   (exp expression?)))

;;;;;;;;;;;;;;;;  unifier  ;;;;;;;;;;;;;;;

(define (unifier ty1 ty2 subst exp)
  (let rec ([ty1 (apply-subst-to-type ty1 subst)]
            [ty2 (apply-subst-to-type ty2 subst)]
            [subst subst])
    (cond
      [(equal? ty1 ty2) subst]
      [(tvar-type? ty1)
       (if (no-occurrence? ty1 ty2)
           (extend-subst subst ty1 ty2)
           (eopl:error 'unifier
                       "no-occurrence violation ~A = ~A in~%~A"
                       (format-type ty1)
                       (format-type ty2)
                       exp))]
      [(tvar-type? ty2)
       (if (no-occurrence? ty2 ty1)
           (extend-subst subst ty2 ty1)
           (eopl:error 'unifier
                       "no-occurrence violation ~A = ~A in~%~A"
                       (format-type ty2)
                       (format-type ty1)
                       exp))]
      [(and (proc-type? ty1)
            (proc-type? ty2))
       (rec (proc-type->ret ty1)
         (proc-type->ret ty2)
         (rec (proc-type->arg ty1)
           (proc-type->arg ty2)
           subst))]
      [else
       (eopl:error 'unifier
                   "unification failure ~A = ~A in~%~A"
                   (format-type ty1)
                   (format-type ty2)
                   exp)])))

(define (no-occurrence? tvar ty)
  (cases type ty
    [proc-type (a b)
               (and (no-occurrence? tvar a)
                    (no-occurrence? tvar b))]
    [tvar-type (s)
               (not (equal? tvar ty))]
    [else #t]))

(define (proc-type->arg x)
  (cases type x
    [proc-type (a b) a]
    [else (eopl:error '??? "???")]))

(define (proc-type->ret x)
  (cases type x
    [proc-type (a b) b]
    [else (eopl:error '??? "???")]))

(define (tvar-type? x)
  (cases type x
    [tvar-type (s) #t]
    [else #f]))

(define (proc-type? x)
  (cases type x
    [proc-type (a b) #t]
    [else #f]))

;;;;;;;;;;;;;;  type checker ;;;;;;;;;;;;;;

(define-datatype answer answer?
  [an-answer
   (ty type?)
   (eql eq-list?)])

(define (type-of-program prg)
  (cases program prg
    [a-program (exp1)
               (cases answer (type-of exp1 (empty-tenv) (empty-eq-list))
                 [an-answer (ty eql)
                            (let loop ([eql eql]
                                       [subst (empty-subst)])
                              (cases eq-list eql
                                [empty-eq-list ()
                                               (apply-subst-to-type ty subst)]
                                [extend-eq-list (eql1 ty1 ty2 exp)
                                                (loop eql1
                                                      (unifier ty1 ty2 subst exp))]))])]))

(define (type-of exp tenv eql)
  (cases expression exp
    [const-exp (n)
               (an-answer (int-type) eql)]
    [var-exp (var)
             (an-answer (apply-tenv tenv var) eql)]
    [diff-exp (exp1 exp2)
              (cases answer (type-of exp1 tenv eql)
                [an-answer (ty1 eql1)
                             (cases answer (type-of exp2
                                                    tenv
                                                    (extend-eq-list eql1 ty1 (int-type) exp1))
                               [an-answer (ty2 eql2)
                                          (an-answer (int-type)
                                                     (extend-eq-list eql2 ty2 (int-type) exp2))])])]
    [zero?-exp (exp1)
               (cases answer (type-of exp1 tenv eql)
                 [an-answer (ty1 eql)
                            (an-answer (bool-type)
                                       (extend-eq-list eql ty1 (int-type) exp))])]
    [if-exp (exp1 exp2 exp3)
            (cases answer (type-of exp1 tenv eql)
              [an-answer (ty1 eql)
                           (cases answer (type-of exp2
                                                  tenv
                                                  (extend-eq-list eql ty1 (bool-type) exp1))
                             [an-answer (ty2 eql)
                                        (cases answer (type-of exp3 tenv eql)
                                          [an-answer (ty3 eql)
                                                     (an-answer ty2
                                                                (extend-eq-list eql ty2 ty3 exp1))])])])]
    [let-exp (var exp1 body)
             (cases answer (type-of exp1 tenv eql)
               [an-answer (ty1 eql)
                          (type-of body
                                   (extend-tenv var ty1 tenv)
                                   eql)])]
    [proc-exp (var otype body)
              (let ([var-type (otype->type otype)])
                (cases answer (type-of body
                                       (extend-tenv var var-type tenv)
                                       eql)
                  [an-answer (body-type eql)
                             (an-answer 
                              (proc-type var-type body-type)
                              eql)]))]
    [call-exp (exp1 exp2)
              (let ([ret-type (new-tvar-type)])
                (cases answer (type-of exp1 tenv eql)
                  [an-answer (ty1 eql)
                             (cases answer (type-of exp2 tenv eql)
                               [an-answer (ty2 eql)
                                          (an-answer ret-type
                                                     (extend-eq-list eql
                                                                     ty1
                                                                     (proc-type ty2 ret-type)
                                                                     exp))])]))]
    [letrec-exp (ret-ty name var arg-ty body exp1)
                (let* ([ret-type (otype->type ret-ty)]
                      [arg-type (otype->type arg-ty)]
                      [tenv1 (extend-tenv name (proc-type arg-type ret-type) tenv)])
                  (cases answer (type-of body
                                         (extend-tenv var arg-type tenv1)
                                         eql)
                    [an-answer (body-type eql)
                               (type-of exp1
                                        tenv1
                                        (extend-eq-list eql body-type ret-type body))]))]))

(define (otype->type o)
  (cases optional-type o
    [no-type () (new-tvar-type)]
    [a-type (ty) ty]))

(define new-tvar-type
  (let ([i 0])
    (lambda ()
      (set! i (+ i 1))
      (tvar-type i))))

(define (format-tvar sn)
  (string->symbol (string-append "t" (number->string sn))))

(define (format-type ty)
  (cases type ty
    [int-type () 'int]
    [bool-type () 'bool]
    [proc-type (argty retty)
               (list (format-type argty)
                     '->
                     (format-type retty))]
    [tvar-type (sn)
               (format-tvar sn)]))

;;;;;;;;;;;;;;;;;;;;;  test  ;;;;;;;;;;;;;;;;;;;;;;

(define (type-equal? s1 s2)
  (equal? (apply-subst-to-sexp (canonical-subst s1) s1)
          (apply-subst-to-sexp (canonical-subst s2) s2)))

(define (canonical-subst s)
  (let loop ([s s] [table '()])
    (cond
      [(null? s) table]
      [(tvar-type-sym? s)
       (cond
         [(assq s table) table]
         [else
          (cons (cons s (format-tvar (length table)))
                table)])]
      [(pair? s)
       (loop (cdr s)
             (loop (car s) table))]
      [else table])))

(define (tvar-type-sym? s)
  (and (symbol? s)
       (char-numeric? (car (reverse (string->list (symbol->string s)))))))

(define (apply-subst-to-sexp subst s)
  (cond
    [(null? s) s]
    [(tvar-type-sym? s)
     (cdr (assq s subst))]
    [(pair? s)
     (cons (apply-subst-to-sexp subst (car s))
           (apply-subst-to-sexp subst (cdr s)))]
    [else s]))

;;;;;;;;;;;;;;;;;;

(define (test type prg)
  (let ([ty0 (format-type (type-of-program (scan&parse prg)))])
    (if (type-equal? ty0 type)
        (eopl:printf "~A = ~A~%"
                     ty0 type)
        (eopl:error 'test
                    "~A != ~A~%"
                    ty0 type))))

(test '(t0 -> t0)
      "
proc (x:?) x")

(test '((int -> int) -> (int -> int))
      "
proc (f:?) proc(x:?) -((f 3),(f x))")

(test 'int
      "
let add = proc (x:?)
           proc (y:?)
            -(x, -(0, y))
in
 letrec
  ? fib(n:?) =
     if zero?(n) then 0
     else if zero?(-(n, 1)) then 1
     else ((add (fib -(n,1))) (fib -(n,2)))
in (fib 10)
")

(provide run)