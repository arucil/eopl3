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
     ("letrec" (arbno optional-type identifier "("
                      (separated-list identifier ":" optional-type ",") ")" "=" expression)
               "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ":" optional-type ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
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
     ("(" (arbno type) "->" type ")")
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
   (vars identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (bodies (list-of expression?))
   (env environment?)))

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var val env)
                (if (eqv? var svar)
                    val
                    (apply-env env svar))]
    [extend-env-rec (pnames bvarss bodies e)
                    (let loop ([pnames pnames]
                               [bvarss bvarss]
                               [bodies bodies])
                      (cond
                        [(null? pnames)
                         (apply-env e svar)]
                        [(eqv? svar (car pnames))
                         (proc-val (procedure (car bvarss)
                                              (car bodies)
                                              env))]
                        [else
                         (loop (cdr pnames)
                               (cdr bvarss)
                               (cdr bodies))]))]))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars)
                   (cdr vals)
                   (extend-env (car vars)
                               (car vals)
                               env))))

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

(define (extend-tenv* vars tys tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars)
                    (cdr tys)
                    (extend-tenv (car vars)
                                 (car tys)
                                 tenv))))

;;;;;;;;;;;;;;;;;;  proc  ;;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure p vals)
  (cases proc p
    [procedure (vars body env)
               (value-of body
                         (extend-env* vars vals env))]))

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
    [let-exp (vars exps body)
             (value-of body
                       (extend-env* vars
                                    (map (lambda (x)
                                           (value-of x env))
                                         exps)
                                   env))]
    [letrec-exp (ret-tys p-names b-varss arg-tys bodies exp1)
                (value-of exp1 (extend-env-rec p-names b-varss bodies env))]
    
    ;;; procedures
    [proc-exp (vars arg-types exp1)
              (proc-val (procedure vars exp1 env))]
    
    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]
    ))

;;;;;;;;;;;;;  subst  ;;;;;;;;;;;;;;;;;

(define (apply-one-subst ty0 tvar ty1)
  (cases type ty0
    [proc-type (ts t1)
               (proc-type (map (lambda (x)
                                 (apply-one-subst x tvar ty1))
                               ts)
                          (apply-one-subst t1 tvar ty1))]
    [tvar-type (sn)
               (if (equal? ty0 tvar) ty1 ty0)]
    [else ty0]))

(define (apply-subst-to-type ty subst)
  (cases type ty
    [proc-type (ts t1)
               (proc-type (map (lambda (x)
                                 (apply-subst-to-type x subst))
                               ts)
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

(define (format-subst subst)
  (unless (null? subst)
    (format-subst (cdr subst))
    (eopl:printf "~A = ~A~%"
                 (format-type (caar subst))
                 (format-type (cdar subst)))))

;;;;;;;;;;;;;;;;  unifier  ;;;;;;;;;;;;;;;

(define (unifier ty1 ty2 subst exp)
  (let ([ty1 (apply-subst-to-type ty1 subst)]
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
       (unless (= (length (proc-type->args ty1))
                  (length (proc-type->args ty2)))
         (eopl:error 'unifier
                     "argument number mismatch ~A != ~A in ~%~A"
                     (length (proc-type->args ty1))
                     (length (proc-type->args ty2))
                     exp))
       (let loop ([args1 (proc-type->args ty1)]
                  [args2 (proc-type->args ty2)]
                  [subst subst])
         (if (null? args1)
             (unifier (proc-type->ret ty1)
                      (proc-type->ret ty2)
                      subst
                      exp)
             (loop (cdr args1)
                   (cdr args2)
                   (unifier (car args1)
                            (car args2)
                            subst
                            exp))))]
      [else
       (eopl:error 'unifier
                   "unification failure ~A = ~A in~%~A"
                   (format-type ty1)
                   (format-type ty2)
                   exp)])))

(define (every? pred ls)
  (cond
    [(null? ls) #t]
    [(pred (car ls))
     (every? pred (cdr ls))]
    [else #f]))

(define (no-occurrence? tvar ty)
  (cases type ty
    [proc-type (a b)
               (and (every? (lambda (x)
                              (no-occurrence? tvar x))
                            a)
                    (no-occurrence? tvar b))]
    [tvar-type (s)
               (not (equal? tvar ty))]
    [else #t]))

(define (proc-type->args x)
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
   (subst substitution?)])

(define (type-of-program prg)
  (cases program prg
    [a-program (exp1)
               (cases answer (type-of exp1 (empty-tenv) (empty-subst))
                 [an-answer (ty subst)
                            (apply-subst-to-type ty subst)])]))

(define (type-of exp tenv subst)
  (cases expression exp
    [const-exp (n)
               (an-answer (int-type) subst)]
    [var-exp (var)
             (an-answer (apply-tenv tenv var) subst)]
    [diff-exp (exp1 exp2)
              (cases answer (type-of exp1 tenv subst)
                [an-answer (ty1 subst1)
                           (let ([subst1 (unifier ty1 (int-type) subst1 exp1)])
                             (cases answer (type-of exp2 tenv subst1)
                               [an-answer (ty2 subst2)
                                          (an-answer (int-type)
                                                     (unifier ty2 (int-type) subst2 exp2))]))])]
    [zero?-exp (exp1)
               (cases answer (type-of exp1 tenv subst)
                 [an-answer (ty1 subst1)
                            (an-answer (bool-type)
                                       (unifier ty1 (int-type) subst1 exp))])]
    [if-exp (exp1 exp2 exp3)
            (cases answer (type-of exp1 tenv subst)
              [an-answer (ty1 subst)
                         (let ([subst (unifier ty1 (bool-type) subst exp1)])
                           (cases answer (type-of exp2 tenv subst)
                             [an-answer (ty2 subst)
                                        (cases answer (type-of exp3 tenv subst)
                                          [an-answer (ty3 subst)
                                                     (an-answer ty2
                                                                (unifier ty2 ty3 subst exp))])]))])]
    [let-exp (vars exps body)
             (let loop ([vars vars]
                        [exps exps]
                        [tenv1 tenv]
                        [subst subst])
               (if (null? vars)
                   (type-of body tenv1 subst)
                   (cases answer (type-of (car exps) tenv subst)
                     [an-answer (ty1 subst)
                                (loop (cdr vars)
                                      (cdr exps)
                                      (extend-tenv (car vars) ty1 tenv1)
                                      subst)])))]
    [proc-exp (vars otypes body)
              (let ([var-types (map otype->type otypes)])
                (cases answer (type-of body
                                       (extend-tenv* vars var-types tenv)
                                       subst)
                  [an-answer (body-type subst)
                             (an-answer 
                              (proc-type var-types body-type)
                              subst)]))]
    [call-exp (exp1 exps)
              (let ([ret-type (new-tvar-type)])
                (cases answer (type-of exp1 tenv subst)
                  [an-answer (ty1 subst)
                             (let loop ([exps exps]
                                        [tys '()]
                                        [subst subst])
                               (if (null? exps)
                                   (an-answer ret-type
                                              (unifier ty1
                                                       (proc-type (reverse tys) ret-type)
                                                       subst exp))
                                   (cases answer (type-of (car exps) tenv subst)
                                     [an-answer (ty1 subst)
                                                (loop (cdr exps)
                                                      (cons ty1 tys)
                                                      subst)])))]))]
    [letrec-exp (ret-tys names varss arg-tyss bodies exp1)
                (let* ([ret-types (map otype->type ret-tys)]
                       [arg-typess (map (lambda (x) (map otype->type x)) arg-tyss)]
                       [tenv1 (extend-tenv* names
                                            (let loop ([arg-typess arg-typess]
                                                       [ret-types ret-types])
                                              (if (null? ret-types)
                                                  '()
                                                  (cons (proc-type (car arg-typess)
                                                                   (car ret-types))
                                                        (loop (cdr arg-typess)
                                                              (cdr ret-types)))))
                                            tenv)])
                  (let loop ([varss varss]
                             [arg-typess arg-typess]
                             [bodies bodies]
                             [ret-types ret-types]
                             [subst subst])
                    (if (null? varss)
                        (type-of exp1 tenv1 subst)
                        (cases answer (type-of (car bodies)
                                               (extend-tenv* (car varss)
                                                             (car arg-typess)
                                                             tenv1)
                                               subst)
                          [an-answer (body-type subst)
                                     (loop (cdr varss)
                                           (cdr arg-typess)
                                           (cdr bodies)
                                           (cdr ret-types)
                                           (unifier body-type (car ret-types) subst (car bodies)))]))))]
    ))

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
    [proc-type (argtys retty)
               (list (map format-type argtys)
                     '->
                     (format-type retty))]
    [tvar-type (sn)
               (format-tvar sn)]
    ))

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

(test '((t0) -> t0)
      "
proc (x:?) x")

(test '((((int) -> int)) -> ((int) -> int))
      "
proc (f:?) proc(x:?) -((f 3),(f x))")

(test 'int
      "
letrec
 ? fib(n:?, k:?) =
    if zero?(n) then (k 0)
    else if zero?(-(n, 1)) then (k 1)
    else (fib -(n, 1)
           proc (n1:?)
            (fib -(n, 2)
              proc (n2:?)
               (k (add n1 n2))))
 ? add(x:?, y:?) = -(x, -(0, y))
in (fib 10 proc (x:?) x)
")

(provide run)