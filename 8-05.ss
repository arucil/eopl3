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
  '((program ((arbno module-definition) expression) a-program)
    
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
    
    (expression (identifier qualified) var-exp)

    (qualified
     ()
     unqualified)

    (qualified
     ("." identifier)
     qualified-var)
    
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

    ;;;;;;;;;;;;;  module  ;;;;;;;;;;;;;;;;

    (module-definition
     ("module" identifier "interface" interface "body" module-body)
     a-module-definition)

    (interface
     ("[" (arbno declaration) "]")
     simple-iface)

    (declaration
     (identifier ":" type)
     val-decl)

    (module-body
     ("[" (arbno definition) "]")
     defns-module-body)

    (module-body
     ("let" (arbno identifier "=" expression) "in"
            "[" (arbno definition) "]")
     let-module-body)

    (module-body
     ("letrec" (arbno type identifier "("
                      (separated-list identifier ":" type ",") ")" "=" expression)
               "in"
            "[" (arbno definition) "]")
     letrec-module-body)

    (definition
     (identifier "=" expression)
     val-defn)


    ;;;;;;;;;;;;;;  type  ;;;;;;;;;;;;;;;;;;

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" (arbno type) "->" type ")")
     proc-type)

    
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;  module  ;;;;;;;;;;;;;;;;

(define-datatype typed-module typed-module?
  [simple-module
   (bindings environment?)])

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-varss (list-of (list-of identifier?)))
   (bodies (list-of expression?))
   (env environment?))
  (extend-env-with-module
   (m-name symbol?)
   (m-val typed-module?)
   (env environment?)))

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var val e)
                (if (eqv? var svar)
                    val
                    (apply-env e svar))]
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
                               (cdr bodies))]))]
    [extend-env-with-module (m-name m-val e)
                            (apply-env e svar)]
    ))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars)
                   (cdr vals)
                   (extend-env (car vars)
                               (car vals)
                               env))))

(define (lookup-qualified-var-in-env m-name var-name env)
  (cases typed-module (lookup-module-name-in-env m-name env)
    [simple-module (bindings)
                   (apply-env bindings var-name)]))

(define (lookup-module-name-in-env m-name env)
  (cases environment env
    [empty-env()
              'error]
    [extend-env (var val e)
                (lookup-module-name-in-env m-name e)]
    [extend-env-rec (a b c e)
                    (lookup-module-name-in-env m-name e)]
    [extend-env-with-module (name val e)
                            (if (eqv? name m-name)
                                val
                                (lookup-module-name-in-env m-name e))]))

;;;;;;;;;;;;;;;  type environment ;;;;;;;;;;

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv
   (var identifier?)
   (ty type?)
   (tenv tenvironment?))
  (extend-tenv-with-module
   (name symbol?)
   (interface interface?)
   (env tenvironment?)))

(define (apply-tenv tenv svar)
  (cases tenvironment tenv
    [empty-tenv ()
     (eopl:error 'apply-tenv "variable ~s is not bound" svar)]
    [extend-tenv (var ty env)
                (if (eqv? var svar)
                    ty
                    (apply-tenv env svar))]
    [extend-tenv-with-module (name i e)
                            (apply-tenv e svar)]
    ))

(define (extend-tenv* vars tys tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars)
                    (cdr tys)
                    (extend-tenv (car vars)
                                 (car tys)
                                 tenv))))

(define (lookup-qualified-var-in-tenv m-name var-name tenv)
  (cases interface (lookup-module-name-in-tenv m-name tenv)
    [simple-iface (decls)
                  (lookup-var-name-in-decls var-name decls)]))

(define (lookup-module-name-in-tenv m-name tenv)
  (cases tenvironment tenv
    [empty-tenv()
              (eopl:error 'type-of
                          "module ~A not bound"
                          m-name)]
    [extend-tenv (var val e)
                (lookup-module-name-in-tenv m-name e)]
    [extend-tenv-with-module (name i e)
                             (if (eqv? name m-name)
                                 i
                                 (lookup-module-name-in-tenv m-name e))]))

(define (module-exists? m-name tenv)
  (cases tenvironment tenv
    [empty-tenv()
               #f]
    [extend-tenv (var val e)
                (module-exists? m-name e)]
    [extend-tenv-with-module (name i e)
                             (if (eqv? name m-name)
                                 #t
                                 (module-exists? m-name e))]))

(define (lookup-var-name-in-decls var-name decls)
  (if (null? decls)
     (eopl:error 'type-of "variable ~A not bound" var-name)
     (cases declaration (car decls)
       [val-decl (var type)
                 (if (eqv? var var-name)
                     type
                     (lookup-var-name-in-decls var-name (cdr decls)))])))

;;;;;;;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;  expval  ;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;;;;

(define (run prog)
  (let ([prg (scan&parse prog)])
    (type-of-program prg)
    (cases program prg
      [a-program (defns exp)
                 (value-of exp (add-module-defns-to-env defns (empty-env)))])))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
              (num-val (- (expval->num (value-of exp1 env))
                          (expval->num (value-of exp2 env))))]
    [var-exp (var q)
             (cases qualified q
               [qualified-var (var1)
                              (lookup-qualified-var-in-env var var1 env)]
               [unqualified ()
                            (apply-env env var)])]
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

(define (add-module-defns-to-env defns env)
  (if (null? defns)
      env
      (cases module-definition (car defns)
        [a-module-definition (m-name iface m-body)
                             (cases interface iface
                               [simple-iface (decls)
                                             (add-module-defns-to-env
                                              (cdr defns)
                                              (extend-env-with-module
                                               m-name
                                               (value-of-module-body decls m-body env)
                                               env))])])))

(define (value-of-module-body decls m-body env)
  (cases module-body m-body
    [defns-module-body (defns)
      (simple-module (defns-to-env decls defns env))]
    [let-module-body (vars exps defns)
                     (simple-module
                      (defns-to-env decls defns
                        (extend-env* vars
                                     (map (lambda (x)
                                            (value-of x env))
                                          exps)
                                     env)))]
    [letrec-module-body (ret-tys names varss arg-tyss bodies defns)
                        (simple-module
                         (defns-to-env decls defns
                           (extend-env-rec names varss bodies env)))]
    ))

(define (defns-to-env decls defns env)
  (if (null? defns)
      (empty-env)
      (cases definition (car defns)
        [val-defn (var exp)
                  (let* ([val (value-of exp env)]
                         [env1 (defns-to-env decls
                                 (cdr defns)
                                 (extend-env var val env))])
                    (if (decl-exists? var decls)
                        (extend-env var val env1)
                        env1))])))

(define (decl-exists? var decls)
  (if (null? decls)
      #f
      (cases declaration (car decls)
        [val-decl (var1 type)
                  (if (eqv? var1 var)
                      #t
                      (decl-exists? var (cdr decls)))])))

;;;;;;;;;;;;;;  type checker ;;;;;;;;;;;;;;

(define (type-of-program prg)
  (cases program prg
    [a-program (defns exp1)
               (type-of exp1 (add-module-defns-to-tenv defns (empty-tenv)))]))

(define (add-module-defns-to-tenv defns tenv)
  (if (null? defns)
      tenv
      (cases module-definition (car defns)
        [a-module-definition (m-name expected-iface m-body)
                             (when (module-exists? m-name tenv)
                               (eopl:error 'type-of
                                           "module ~A duplicates"
                                           m-name))
                             (let ([actual-iface (interface-of m-body tenv)])
                               (if (<:-iface actual-iface expected-iface tenv)
                                   (add-module-defns-to-tenv (cdr defns)
                                                             (extend-tenv-with-module m-name
                                                                                      expected-iface
                                                                                      tenv))
                                   (eopl:error 'type-of
                                               "module ~A  = ~A doesn't satisfy interface ~A"
                                               m-name actual-iface expected-iface)))])))

(define (interface-of m-body tenv)
  (cases module-body m-body
    [defns-module-body (defns)
      (simple-iface (defns-to-decls defns tenv))]
    [let-module-body (vars exps defns)
                     (simple-iface (defns-to-decls defns
                                     (extend-tenv* vars
                                                   (map (lambda (x)
                                                          (type-of x tenv))
                                                        exps)
                                                   tenv)))]
    [letrec-module-body (ret-tys names varss arg-tyss bodies defns)
                        (let ([tenv1 (extend-tenv* names
                                                   (let loop ([arg-tyss arg-tyss]
                                                              [ret-tys ret-tys]
                                                              [tys '()])
                                                     (if (null? ret-tys)
                                                         (reverse tys)
                                                         (loop (cdr arg-tyss)
                                                               (cdr ret-tys)
                                                               (cons (proc-type (car arg-tyss)
                                                                                (car ret-tys))
                                                                     tys))))
                                                   tenv)])
                          (let loop ([ret-tys ret-tys]
                                     [bodies bodies]
                                     [varss varss]
                                     [arg-tyss arg-tyss])
                            (unless (null? bodies)
                              (check-equal-type! (car ret-tys)
                                                 (type-of (car bodies)
                                                          (extend-tenv* (car varss)
                                                                        (car arg-tyss)
                                                                        tenv1))
                                                 (car bodies))))
                          (simple-iface (defns-to-decls defns tenv1)))]
    ))

(define (defns-to-decls defns tenv)
  (if (null? defns)
      '()
      (cases definition (car defns)
        [val-defn (var-name exp)
                  (let ([ty (type-of exp tenv)])
                    (cons (val-decl var-name ty)
                          (defns-to-decls (cdr defns)
                            (extend-tenv var-name ty tenv))))])))

(define (<:-iface iface1 iface2 tenv)
  (cases interface iface1
    [simple-iface (decls1)
                  (cases interface iface2
                    [simple-iface (decls2)
                                  (<:-decls decls1 decls2 tenv)])]))

(define (<:-decls decls1 decls2 tenv)
  (cond
    [(null? decls2) #t]
    [(null? decls1) #f]
    [else
     (if (eqv? (decl->name (car decls1))
               (decl->name (car decls2)))
         (and (equal? (decl->type (car decls1))
                      (decl->type (car decls2)))
              (<:-decls (cdr decls1)
                        (cdr decls2)
                        tenv))
         (<:-decls (cdr decls1)
                   decls2
                   tenv))]))

(define (decl->name decl)
  (cases declaration decl
    [val-decl (var ty)
              var]))

(define (decl->type decl)
  (cases declaration decl
    [val-decl (var ty)
              ty]))

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
                     (format-type retty))]))

(define (type-of exp tenv)
  (cases expression exp
    [const-exp (n)
               (int-type)]
    [var-exp (var q)
             (cases qualified q
               [qualified-var (var1)
                              (lookup-qualified-var-in-tenv var var1 tenv)]
               [unqualified ()
                            (apply-tenv tenv var)])]
    [diff-exp (exp1 exp2)
              (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
              (check-equal-type! (type-of exp2 tenv) (int-type) exp2)
              (int-type)]
    [zero?-exp (exp1)
               (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
               (bool-type)]
    [if-exp (exp1 exp2 exp3)
            (let ([ty1 (type-of exp2 tenv)])
              (check-equal-type! (type-of exp1 tenv)
                                 (bool-type)
                                 exp1)
              (check-equal-type! ty1
                                 (type-of exp3 tenv)
                                 exp)
              ty1)]
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
                             (unless (equal? (length arg-tys)
                                             (length exps))
                               (eopl:error 'type-of
                                           "argument number mismatch, expecting ~A, got ~A"
                                           (length arg-tys)
                                           (length exps)))
                             (let loop ([arg-tys arg-tys]
                                        [exps exps])
                               (unless (null? exps)
                                 (check-equal-type! (car arg-tys)
                                                    (type-of (car exps) tenv)
                                                    (car exps))
                                 (loop (cdr arg-tys)
                                       (cdr exps))))
                             ret-ty]
                  [else
                   (eopl:error 'type-of "exp ~A is ~A rather than proc" exp1 ty1)]))]
    [letrec-exp (ret-tys names varss arg-tyss bodies exp1)
                (let ([tenv1 (extend-tenv*
                              names
                              (let loop ([arg-tyss arg-tyss]
                                         [ret-tys ret-tys]
                                         [tys '()])
                                (if (null? ret-tys)
                                    (reverse tys)
                                    (loop (cdr arg-tyss)
                                          (cdr ret-tys)
                                          (cons (proc-type (car arg-tyss)
                                                           (car ret-tys))
                                                tys))))
                              tenv)])
                  (let loop ([ret-tys ret-tys]
                             [bodies bodies]
                             [varss varss]
                             [arg-tyss arg-tyss])
                    (unless (null? bodies)
                      (check-equal-type! (car ret-tys)
                                         (type-of (car bodies)
                                                  (extend-tenv* (car varss)
                                                                (car arg-tyss)
                                                                tenv1))
                                         (car bodies))))
                  (type-of exp1 tenv1))]
    ))

(provide run)