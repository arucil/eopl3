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
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("letrec" type identifier "(" identifier ":" type ")" "=" expression "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" identifier ":" type ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("from" identifier "take" identifier)
     qualified-var-exp)

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
     ("(" type "->" type ")")
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
   (p-name identifier?)
   (b-var identifier?)
   (body expression?)
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
    [extend-env-rec (pname bvar body e)
                    (if (eqv? svar pname)
                        (proc-val (procedure bvar body env))
                        (apply-env e svar))]
    [extend-env-with-module (m-name m-val e)
                            (apply-env e svar)]
    ))

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
   (var identifier?)
   (body expression?)
   (env environment?)))

(define (apply-procedure p val)
  (cases proc p
    [procedure (var body env)
               (value-of body
                         (extend-env var val env))]))

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
    [var-exp (var)
      (apply-env env var)]
    [zero?-exp (exp1)
               (bool-val (zero? (expval->num (value-of exp1 env))))]
    [if-exp (exp1 exp2 exp3)
      (if (expval->bool (value-of exp1 env))
          (value-of exp2 env)
          (value-of exp3 env))]
    [let-exp (var exp body)
             (value-of body (extend-env var
                                        (value-of exp env)
                                        env))]
    [letrec-exp (ret-ty p-name b-var arg-ty body exp)
                (value-of exp (extend-env-rec p-name b-var body env))]
    [proc-exp (var arg-type exp)
              (proc-val (procedure var exp env))]

    [call-exp (exp1 exp2)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (value-of exp2 env))]
    [qualified-var-exp (m-name var)
                       (lookup-qualified-var-in-env m-name var env)]
    ))

(define (add-module-defns-to-env defns env)
  (if (null? defns)
      env
      (cases module-definition (car defns)
        [a-module-definition (m-name iface m-body)
                             (add-module-defns-to-env (cdr defns)
                                                      (extend-env-with-module m-name
                                                                              (value-of-module-body m-body env)
                                                                              env))])))

(define (value-of-module-body m-body env)
  (cases module-body m-body
    [defns-module-body (defns)
      (simple-module (defns-to-env defns env))]))

(define (defns-to-env defns env)
  (if (null? defns)
      (empty-env)
      (cases definition (car defns)
        [val-defn (var exp)
                  (let ([val (value-of exp env)])
                    (extend-env var val
                                (defns-to-env (cdr defns)
                                  (extend-env var val env))))])))

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
      (simple-iface (defns-to-decls defns tenv))]))

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
    [proc-type (argty retty)
               (list (format-type argty)
                     '->
                     (format-type retty))]))

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
            (let ([ty1 (type-of exp2 tenv)])
              (check-equal-type! (type-of exp1 tenv)
                                 (bool-type)
                                 exp1)
              (check-equal-type! ty1
                                 (type-of exp3 tenv)
                                 exp)
              ty1)]
    [let-exp (var exp1 body)
             (type-of body
                      (extend-tenv var
                                   (type-of exp1 tenv)
                                   tenv))]
    [proc-exp (var arg-type body)
              (proc-type arg-type
                         (type-of body
                                  (extend-tenv var arg-type tenv)))]
    [call-exp (exp1 exp2)
              (let ([ty1 (type-of exp1 tenv)])
                (cases type ty1
                  [proc-type (arg-ty ret-ty)
                             (check-equal-type! arg-ty
                                                (type-of exp2 tenv)
                                                exp2)
                             ret-ty]
                  [else
                   (eopl:error 'type-of "exp ~A is ~A rather than proc" exp1 ty1)]))]
    [letrec-exp (ret-ty name var arg-ty body exp1)
                (let ([tenv1 (extend-tenv name (proc-type arg-ty ret-ty) tenv)])
                  (check-equal-type! ret-ty
                                     (type-of body
                                              (extend-tenv var arg-ty tenv1))
                                     body)
                  (type-of exp1 tenv1))]
    [qualified-var-exp (m-name var)
                       (lookup-qualified-var-in-tenv m-name var tenv)]
    ))

(provide run)