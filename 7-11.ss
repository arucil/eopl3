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
     ("letrec" (arbno type identifier "("
                      (separated-list identifier ":" type ",") ")" "=" expression)
               "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ":" type ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;;;;;;;;;;;   explicit reference ;;;;;;;;;

    (expression
     ("newref" "(" expression ")")
     newref-exp)

    (expression
     ("deref" "(" expression ")")
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)

    (expression
     ("pair" "(" expression "," expression ")")
     pair-exp)

    (expression
     ("left" "(" expression ")")
     left-exp)

    (expression
     ("right" "(" expression ")")
     right-exp)

    (expression
     ("setleft" "(" expression "," expression ")")
     setleft-exp)

    (expression
     ("setright" "(" expression "," expression ")")
     setright-exp)

    ;;;;;  type  ;;;;;;;;;;;;;;

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
     ("pairof" type type)
     pair-type)

    (type
     ("refto" type)
     ref-type)

    (type
     ("void")
     void-type)
    
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
  val)

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec*
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
    [extend-env-rec* (pnames bvarss bodies e)
                     (let loop ([pnames pnames]
                                [bvarss bvarss]
                                [bodies bodies])
                       (cond
                         [(null? pnames)
                          (apply-env e svar)]
                         [(eqv? (car pnames) svar)
                          (proc-val (procedure (car bvarss)
                                               (car bodies)
                                               env))]
                         [else
                          (loop (cdr pnames)
                                (cdr bvarss)
                                (cdr bodies))]))]
    ))

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
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-tenv (var ty env)
                (if (eqv? var svar)
                    ty
                    (apply-tenv env svar))]))

(define (extend-tenv* vars types tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars)
                    (cdr types)
                    (extend-tenv (car vars)
                                 (car types)
                                 tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (pair-val
   (ref reference?))
  (ref-val
   (ref reference?))
  )

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
    [pair-val (ref) ref]
    [else
     (eopl:error 'expval->pair "expval ~A is not pair" val)]))

(define (expval->ref val)
  (cases expval val
    [ref-val (ref) ref]
    [else
     (eopl:error 'expval->ref "expval ~A is not ref" val)]))

(define (apply-procedure p vals)
  (cases proc p
    [procedure (vars body env)
               (value-of body
                         (extend-env* vars vals env))]))

(define (run prog)
  (let ([prg (scan&parse prog)])
    (type-of-program prg)
    (init-store)
    (cases program prg
      [a-program (exp)
                 (value-of exp (empty-env))])))

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
    [diff-exp (exp1 exp2)
      (value-of-arith - env exp1 exp2)]
    [var-exp (var)
      (apply-env env var)]
    [zero?-exp (exp)
      (value-of-arith zero? env exp)]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (vars exps body)
             (value-of body (extend-env* vars
                                         (map (lambda (x)
                                                (value-of x env))
                                              exps)
                                         env))]
    [letrec-exp (ret-tys p-names b-varss arg-tys bodies exp)
                (value-of exp (extend-env-rec* p-names b-varss bodies env))]

    ;;; procedures
    [proc-exp (vars arg-types exp)
              (proc-val (procedure vars exp env))]

    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]
    ;;; reference
    [newref-exp (exp1)
                (ref-val (newref (value-of exp1 env)))]
    [deref-exp (exp1)
               (deref (expval->ref (value-of exp1 env)))]
    [setref-exp (exp1 exp2)
                (setref! (expval->ref (value-of exp1 env))
                         (value-of exp2 env))
                (num-val 1)]
    [pair-exp (exp1 exp2)
              (let ([ref1 (newref (value-of exp1 env))])
                (newref (value-of exp2 env))
                (pair-val ref1))]
    [left-exp (exp1)
              (deref (expval->pair (value-of exp1 env)))]
    [right-exp (exp1)
               (deref (+ 1 (expval->pair (value-of exp1 env))))]
    [setleft-exp (exp1 exp2)
                 (setref! (expval->pair (value-of exp1 env))
                          (value-of exp2 env))]
    [setright-exp (exp1 exp2)
                  (setref! (+ 1 (expval->pair (value-of exp1 env)))
                           (value-of exp2 env))]
    ))

;;;;;;;;;;;;;;  type checker ;;;;;;;;;;;;;;

(define (type-of-program prg)
  (cases program prg
    [a-program (exp1)
               (type-of exp1 (empty-tenv))]))

(define (check-equal-type! ty1 ty2 exp)
  (unless (equal? ty1 ty2)
    (eopl:error 'check-equal-type!
                "Types didn't match: ~s != ~a in~%~a"
                (format-type ty1)
                (format-type ty2)
                exp)))

(define (format-type ty)
  (cases type ty
    [int-type () 'int]
    [bool-type () 'bool]
    [proc-type (argtys retty)
               (list (map format-type argtys)
                     '->
                     (format-type retty))]
    [ref-type (ty)
              (list 'refto
                    (format-type ty))]
    [void-type ()
               (list 'void)]
    [pair-type (ty1 ty2)
               (list 'pairof
                     (format-type ty1)
                     (format-type ty2))]
    ))

(define (type-of exp tenv)
  (cases expression exp
    [const-exp (n)
               (int-type)]
    [var-exp (var)
             (apply-tenv tenv var)]
    [diff-exp (exp1 exp2)
              (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
              (check-equal-type! (type-of exp2 tenv) (int-type) exp2)
              (int-type)]
    [zero?-exp (exp1)
               (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
               (bool-type)]
    [if-exp (exp1 exp2 exp3)
            (and (check-equal-type! (type-of exp1 tenv)
                                    (bool-type)
                                    exp1)
                 (let ([ty1 (type-of exp2 tenv)])
                   (check-equal-type! ty1
                                      (type-of exp3 tenv)
                                      exp)
                   ty1))]
    [let-exp (vars exps body)
             (type-of body
                      (extend-tenv* vars
                                    (map (lambda (x)
                                           (type-of x tenv))
                                         exps)
                                    tenv))]
    [proc-exp (vars arg-types body)
              (proc-type arg-types
                         (type-of body
                                  (extend-tenv* vars arg-types tenv)))]
    [call-exp (exp1 exps)
              (let ([ty1 (type-of exp1 tenv)])
                (cases type ty1
                  [proc-type (arg-tys ret-ty)
                             (unless (= (length arg-tys) (length exps))
                               (eopl:error 'type-of
                                           "argument number mismatch, expecting ~A, got ~A"
                                           (length arg-tys)
                                           (length exps)))
                             (let loop ([exps exps]
                                        [tys arg-tys])
                               (unless (null? exps)
                                 (check-equal-type! (car tys)
                                                    (type-of (car exps) tenv)
                                                    (car exps))
                                 (loop (cdr exps)
                                       (cdr tys))))
                             ret-ty]
                  [else
                   (eopl:error 'type-of "exp ~A is ~A rather than proc" exp1 (format-type ty1))]))]
    [letrec-exp (ret-tys names varss arg-tyss bodies exp1)
                (let ([tenv1 (extend-tenv* names
                                           (let loop ([arg-tyss arg-tyss]
                                                      [ret-tys ret-tys]
                                                      [procs '()])
                                             (if (null? arg-tyss)
                                                 (reverse procs)
                                                 (loop (cdr arg-tyss)
                                                       (cdr ret-tys)
                                                       (cons (proc-type (car arg-tyss)
                                                                        (car ret-tys))
                                                             procs))))
                                           tenv)])
                  (let loop ([bodies bodies]
                             [ret-tys ret-tys]
                             [varss varss]
                             [arg-tyss arg-tyss])
                    (unless (null? bodies)
                      (check-equal-type! (car ret-tys)
                                         (type-of (car bodies)
                                                  (extend-tenv* (car varss)
                                                                (car arg-tyss)
                                                                tenv1))
                                         (car bodies))
                      (loop (cdr bodies)
                            (cdr ret-tys)
                            (cdr varss)
                            (cdr arg-tyss))))
                  (type-of exp1 tenv1))]
    [left-exp (exp1)
              (let ([ty (type-of exp1 tenv)])
                (cases type ty
                  [pair-type (t1 t2)
                             t1]
                  [else
                   (eopl:error 'type-of "exp ~A is ~A rather than pair"
                               exp1 (format-type ty))]))]
    [right-exp (exp1)
               (let ([ty (type-of exp1 tenv)])
                 (cases type ty
                   [pair-type (t1 t2)
                              t2]
                   [else
                    (eopl:error 'type-of "exp ~A is ~A rather than pair"
                                exp1 (format-type ty))]))]
    [pair-exp (exp1 exp2)
              (pair-type (type-of exp1 tenv)
                         (type-of exp2 tenv))]
    [setleft-exp (exp1 exp2)
                 (type-of exp2 tenv)
                 (let ([ty1 (type-of exp1 tenv)])
                   (cases type ty1
                     [pair-type (t1 t2)
                                (void-type)]
                     [else
                      (eopl:error 'type-of "exp ~A is ~A rather than pair"
                                  exp1 (format-type ty1))]))]
    [setright-exp (exp1 exp2)
                  (type-of exp2 tenv)
                  (let ([ty1 (type-of exp1 tenv)])
                    (cases type ty1
                      [pair-type (t1 t2)
                                 (void-type)]
                      [else
                       (eopl:error 'type-of "exp ~A is ~A rather than pair"
                                   exp1 (format-type ty1))]))]
    [newref-exp (exp1)
            (ref-type (type-of exp1 tenv))]
    [deref-exp (exp1)
           (let ([ty1 (type-of exp1 tenv)])
             (cases type ty1
               [ref-type (t1)
                         t1]
               [else
                (eopl:error 'type-of "exp ~A is ~A rather than ref"
                            exp1 (format-type ty1))]))]
    [setref-exp (exp1 exp2)
                (let ([ty1 (type-of exp1 tenv)])
                  (cases type ty1
                    [ref-type (t1)
                              (check-equal-type! t1
                                                 (type-of exp2 tenv)
                                                 exp2)
                              (void-type)]
                    [else
                     (eopl:error 'type-of "exp ~A is ~A rather than ref"
                                 exp1 (format-type ty1))]))]
    ))

(provide run)