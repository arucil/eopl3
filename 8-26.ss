#lang eopl

(require "racket-lib.ss")

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "+" "_" "-" "*" "/" "?")))
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

    (interface
     ("(" "(" identifier ":" interface ")" "=>" interface ")")
     proc-iface)

    (declaration
     (identifier ":" type)
     val-decl)

    (declaration
     ("opaque" identifier)
     opaque-type-decl)

    (declaration
     ("transparent" identifier "=" type)
     transparent-type-decl)

    (module-body
     ("[" (arbno definition) "]")
     defns-module-body)

    (module-body
     ("module-proc" "(" identifier ":" interface ")" module-body)
     proc-module-body)

    (module-body
     (identifier)
     var-module-body)

    (module-body
     ("(" module-body module-body ")")
     app-module-body)

    (definition
     (identifier "=" expression)
     val-defn)

    (definition
     ("type" identifier "=" type)
     type-defn)

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

    (type
     (identifier)
     named-type)

    (type
     ("from" identifier "take" identifier)
     qualified-type)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;  module  ;;;;;;;;;;;;;;;;

(define-datatype typed-module typed-module?
  [simple-module
   (bindings environment?)]
  [proc-module
   (b-var identifier?)
   (body module-body?)
   (env environment?)]
  )

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
                   (apply-env bindings var-name)]
    [proc-module (a b c)
                 (eopl:error 'value-of
                             "unreachable: from ~A take ~A"
                             m-name var-name)]
    ))

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
   (env tenvironment?))
  (extend-tenv-with-type
   (name identifier?)
   (type type?)
   (env tenvironment?))
  )

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
    [extend-tenv-with-type (name i e)
                           (apply-tenv e svar)]
    ))

(define (lookup-qualified-var-in-tenv m-name var-name tenv)
  (cases interface (lookup-module-name-in-tenv m-name tenv)
    [simple-iface (decls)
                  (lookup-var-name-in-decls var-name decls)]
    [proc-iface (name iface1 iface2)
                (eopl:error 'type-of
                            "attempt to refer to qualified variable from procedure module:~%from ~A take ~A"
                            m-name var-name)]
    ))

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
                                 (lookup-module-name-in-tenv m-name e))]
    [extend-tenv-with-type (var val e)
                           (lookup-module-name-in-tenv m-name e)]
    ))

(define (lookup-type-name-in-tenv name tenv)
  (cases tenvironment tenv
    [empty-tenv()
              (eopl:error 'type-of
                          "type ~A not bound"
                          name)]
    [extend-tenv (var val e)
                (lookup-type-name-in-tenv name e)]
    [extend-tenv-with-module (name1 i e)
                             (lookup-type-name-in-tenv name e)]
    [extend-tenv-with-type (var val e)
                           (if (equal? var name)
                               val
                               (lookup-type-name-in-tenv name e))]
    ))

(define (lookup-qualified-type-in-tenv m-name t-name tenv)
  (cases interface (lookup-module-name-in-tenv m-name tenv)
    [simple-iface (decls)
                  (lookup-type-name-in-decls t-name decls)]
    [proc-iface (name iface1 iface2)
                (eopl:error 'type-of
                            "attempt to refer to qualified type from procedure module:~%from ~A take ~A"
                            m-name t-name)]
    ))

(define (lookup-var-name-in-decls var-name decls)
  (if (null? decls)
      (eopl:error 'type-of "variable ~A not bound" var-name)
      (cases declaration (car decls)
        [val-decl (var type)
                  (if (eqv? var var-name)
                      type
                      (lookup-var-name-in-decls var-name (cdr decls)))]
        [else
         (lookup-var-name-in-decls var-name (cdr decls))]
        )))

(define (lookup-type-name-in-decls var-name decls)
  (if (null? decls)
      (eopl:error 'type-of "type ~A not bound" var-name)
      (cases declaration (car decls)
        [val-decl (var type)
                  (if (eqv? var var-name)
                      type
                      (lookup-type-name-in-decls var-name (cdr decls)))]
        [transparent-type-decl (name type)
                               (if (eqv? name var-name)
                                   type
                                   (lookup-type-name-in-decls var-name (cdr decls)))]
        [else
         (eopl:error 'lookup-type-name-in-decls
                     "unreachable ~A"
                     var-name)]
        )))

(define (expand-type ty tenv)
  (cases type ty
    [int-type () ty]
    [bool-type () ty]
    [proc-type (arg-ty ret-ty)
               (proc-type (expand-type arg-ty tenv)
                          (expand-type ret-ty tenv))]
    [named-type (name)
                (lookup-type-name-in-tenv name tenv)]
    [qualified-type (m-name t-name)
                    (lookup-qualified-type-in-tenv m-name t-name tenv)]))

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
                             (add-module-defns-to-env
                              (cdr defns)
                              (extend-env-with-module
                               m-name
                               (value-of-module-body m-body env)
                               env))])))

(define (value-of-module-body m-body env)
  (cases module-body m-body
    [defns-module-body (defns)
      (simple-module (defns-to-env defns env))]
    [var-module-body (m-name)
                     (lookup-module-name-in-env m-name env)]
    [proc-module-body (m-name m-type m-body)
                      (proc-module m-name m-body env)]
    [app-module-body (rator rand)
                     (let ([rator-val (value-of-module-body rator env)])
                       (cases typed-module rator-val
                         [proc-module (m-name m-body env1)
                                      (value-of-module-body
                                       m-body
                                       (extend-env-with-module
                                        m-name
                                        (value-of-module-body rand env)
                                        env1))]
                         [else
                          (eopl:error 'value-of
                                      "bad module application ~A"
                                      rator-val)]))]
    ))

(define (defns-to-env defns env)
  (if (null? defns)
      (empty-env)
      (cases definition (car defns)
        [val-defn (var exp)
                  (let ([val (value-of exp env)])
                    (extend-env var val
                                (defns-to-env (cdr defns)
                                  (extend-env var val env))))]
        [else
         (defns-to-env (cdr defns) env)]
        )))

;;;;;;;;;;;;;;  type checker ;;;;;;;;;;;;;;

(define (type-of-program prg)
  (cases program prg
    [a-program (defns exp1)
               (type-of exp1 (add-module-defns-to-tenv defns (empty-tenv)))]))

(define-datatype answer answer?
  [an-answer
   (tenv tenvironment?)
   (iface interface?)])

(define (add-module-defns-to-tenv defns tenv)
  (if (null? defns)
      tenv
      (cases module-definition (car defns)
        [a-module-definition (m-name expected-iface m-body)
                             (cases answer (interface-of m-body tenv)
                               [an-answer (tenv actual-iface)
                                          (if (<:-iface actual-iface expected-iface tenv)
                                              (add-module-defns-to-tenv
                                               (cdr defns)
                                               (extend-tenv-with-module
                                                m-name
                                                (expand-iface m-name expected-iface tenv)
                                                tenv))
                                              (eopl:error 'type-of
                                                          "module ~A = ~A doesn't satisfy interface ~A"
                                                          m-name actual-iface expected-iface))])])))

(define (interface-of m-body tenv)
  (cases module-body m-body
    [defns-module-body (defns)
      (an-answer tenv (simple-iface (defns-to-decls defns tenv)))]
    [var-module-body (m-name)
                     (an-answer tenv (lookup-module-name-in-tenv m-name tenv))]
    [proc-module-body (rand-name rand-iface m-body)
                      (cases answer (interface-of m-body
                                                  (extend-tenv-with-module
                                                    rand-name
                                                    (expand-iface rand-name rand-iface tenv)
                                                    tenv))
                        [an-answer (tenv result-iface)
                                   (an-answer tenv
                                              (proc-iface rand-name rand-iface result-iface))])]
    [app-module-body (rator rand)
                     (cases answer (interface-of rator tenv)
                       [an-answer (tenv rator-iface)
                                  (cases interface rator-iface
                                    [simple-iface (decls)
                                                  (eopl:error 'type-of
                                                              "attempt to apply simple module ~A"
                                                              rator)]
                                    [proc-iface (param-name param-iface result-iface)
                                                (cases answer (interface-of rand tenv)
                                                  [an-answer (tenv rand-iface)
                                                             (if (<:-iface rand-iface param-iface tenv)
                                                                 (let ([rand-name (new-module-name '%module)])
                                                                   (an-answer
                                                                    (extend-tenv-with-module
                                                                     rand-name
                                                                     (expand-iface rand-name rand-iface tenv)
                                                                     tenv)
                                                                    (rename-in-iface
                                                                     result-iface
                                                                     param-name
                                                                     rand-name)))
                                                                 (eopl:error
                                                                  'type-of
                                                                  "bad module application ~A not <: ~A in~%~A"
                                                                  rand-iface param-iface m-body))])])])]
    ))

(define (rename-in-iface iface var0 var1)
  (cases interface iface
    [simple-iface (decls)
                  (simple-iface (rename-in-decls decls var0 var1))]
    [proc-iface (param-name param-iface result-iface)
                (proc-iface param-name
                            (rename-in-iface param-iface var0 var1)
                            (if (eqv? param-name var0)
                                result-iface
                                (rename-in-iface result-iface var0 var1)))]
    ))

(define (rename-in-decls decls var0 var1)
  (if (null? decls)
      '()
      (cases declaration (car decls)
        [val-decl (name ty)
                  (cons (val-decl name (rename-in-type ty var0 var1))
                        (rename-in-decls (cdr decls) var0 var1))]
        [transparent-type-decl (name ty)
                               (cons (transparent-type-decl name (rename-in-type ty var0 var1))
                                     (if (eqv? name var0)
                                         (cdr decls)
                                         (rename-in-decls (cdr decls) var0 var1)))]
        [opaque-type-decl (name)
                          (cons (car decls)
                                (if (eqv? name var0)
                                    (cdr decls)
                                    (rename-in-decls (cdr decls) var0 var1)))]
        )))

(define (rename-in-type ty var0 var1)
  (cases type ty
    [named-type (name)
                (if (eqv? name var0)
                    (named-type var1)
                    ty)]
    [qualified-type (m-name t-name)
                    (if (eqv? m-name var0)
                        (qualified-type var1 t-name)
                        ty)]
    [proc-type (arg-ty ret-ty)
               (proc-type (rename-in-type arg-ty var0 var1)
                          (rename-in-type ret-ty var0 var1))]
    [else ty]))

(define (defns-to-decls defns tenv)
  (if (null? defns)
      '()
      (cases definition (car defns)
        [val-defn (var-name exp)
                  (let ([ty (type-of exp tenv)])
                    (cons (val-decl var-name ty)
                          (defns-to-decls (cdr defns)
                            (extend-tenv var-name ty tenv))))]
        [type-defn (name ty)
                   (cons (transparent-type-decl name ty)
                         (defns-to-decls
                           (cdr defns)
                           (extend-tenv-with-type name (expand-type ty tenv) tenv)))]
        )))

(define (expand-iface m-name iface tenv)
  (cases interface iface
    [simple-iface (decls)
                  (simple-iface (expand-decls m-name decls tenv))]
    [proc-iface (name aiface riface)
                iface]
    ))

(define (expand-decls m-name decls internal-tenv)
  (if (null? decls)
      '()
      (cases declaration (car decls)
        [opaque-type-decl (t-name)
                          (let ([ty1 (qualified-type m-name t-name)])
                            (cons
                             (transparent-type-decl t-name ty1)
                             (expand-decls m-name
                                           (cdr decls)
                                           (extend-tenv-with-type
                                            t-name ty1 internal-tenv))))]
        [transparent-type-decl (t-name ty)
                               (let ([ty1 (expand-type ty internal-tenv)])
                                 (cons
                                  (transparent-type-decl t-name ty1)
                                  (expand-decls m-name
                                                (cdr decls)
                                                (extend-tenv-with-type
                                                 t-name ty1 internal-tenv))))]
        [val-decl (name ty)
                  (cons (val-decl name (expand-type ty internal-tenv))
                        (expand-decls
                         m-name
                         (cdr decls)
                         internal-tenv))])))

(define (<:-iface iface1 iface2 tenv)
  (cases interface iface1
    [simple-iface (decls1)
                  (cases interface iface2
                    [simple-iface (decls2)
                                  (<:-decls decls1 decls2 tenv)]
                    [proc-iface (a b c) #f])]
    [proc-iface (param-name1 param-iface1 result-iface1)
                (cases interface iface2
                  [simple-iface (a) #f]
                  [proc-iface (param-name2 param-iface2 result-iface2)
                              (let ([new-name (new-module-name param-name1)])
                                (and
                                 (<:-iface param-iface2 param-iface1 tenv)
                                 (<:-iface (rename-in-iface result-iface1 param-name1 new-name)
                                           (rename-in-iface result-iface2 param-name2 new-name)
                                           (extend-tenv-with-module new-name
                                                                    (expand-iface new-name param-iface1 tenv)
                                                                    tenv))))])]
    ))

(define new-module-name
  (let ([i 0])
    (lambda (p)
      (set! i (+ i 1))
      (string->symbol
       (string-append
        (symbol->string p)
        (number->string i))))))

(define (<:-decls decls1 decls2 tenv)
  (cond
    [(null? decls2) #t]
    [(null? decls1) #f]
    [else
     (if (eqv? (decl->name (car decls1))
               (decl->name (car decls2)))
         (and (<:-decl (car decls1)
                       (car decls2)
                       tenv)
              (<:-decls (cdr decls1)
                        (cdr decls2)
                        (extend-tenv-with-decl (car decls1)
                                               tenv)))
         (<:-decls (cdr decls1)
                   decls2
                   (extend-tenv-with-decl (car decls1)
                                          tenv)))]))

(define (extend-tenv-with-decl decl tenv)
  (cases declaration decl
    [val-decl (a b) tenv]
    [transparent-type-decl (name ty)
                           (extend-tenv-with-type name (expand-type ty tenv) tenv)]
    [opaque-type-decl (name)
                      (extend-tenv-with-type name (qualified-type (new-module-name '%module) name) tenv)]))

(define (<:-decl decl1 decl2 tenv)
  (or (and (val-decl? decl1)
           (val-decl? decl2)
           (equiv-type? (decl->type decl1)
                        (decl->type decl2)
                        tenv))
      (and (transparent-type-decl? decl1)
           (or (opaque-type-decl? decl2)
               (and (transparent-type-decl? decl2)
                    (equiv-type? (decl->type decl1)
                                 (decl->type decl2)
                                 tenv))))
      (and (opaque-type-decl? decl1)
           (opaque-type-decl? decl2))))

(define (val-decl? decl)
  (cases declaration decl
    [val-decl (a b) #t]
    [else #f]))

(define (transparent-type-decl? decl)
  (cases declaration decl
    [transparent-type-decl (a b) #t]
    [else #f]))

(define (opaque-type-decl? decl)
  (cases declaration decl
    [opaque-type-decl (a) #t]
    [else #f]))

(define (equiv-type? ty1 ty2 tenv)
  (equal? (expand-type ty1 tenv)
          (expand-type ty2 tenv)))

(define (decl->name decl)
  (cases declaration decl
    [val-decl (var ty)
              var]
    [opaque-type-decl (var)
                      var]
    [transparent-type-decl (var ty)
                           var]
    ))

(define (decl->type decl)
  (cases declaration decl
    [val-decl (var ty)
              ty]
    [transparent-type-decl (var ty)
                           ty]
    [opaque-type-decl (var)
                      (eopl:error 'decl->type
                                  "unreachable ~A"
                                  decl)]
    ))

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
                     (format-type retty))]
    [named-type (var)
                var]
    [qualified-type (m-name t-name)
                    (string->symbol
                     (string-append
                      "from "
                      (symbol->string m-name)
                      " take "
                      (symbol->string t-name)))]
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
                                   (expand-type (type-of exp1 tenv) tenv)
                                   tenv))]
    [proc-exp (var arg-type body)
              (proc-type (expand-type arg-type tenv)
                         (type-of body
                                  (extend-tenv var (expand-type arg-type tenv) tenv)))]
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
                (let ([tenv1 (extend-tenv name (expand-type (proc-type arg-ty ret-ty) tenv) tenv)])
                  (check-equal-type! (expand-type ret-ty tenv)
                                     (type-of body
                                              (extend-tenv var (expand-type arg-ty tenv) tenv1))
                                     body)
                  (type-of exp1 tenv1))]
    [qualified-var-exp (m-name var)
                       (lookup-qualified-var-in-tenv m-name var tenv)]
    ))

(provide run)

(display
 (equal?
  (num-val 2)
  (run "
module to-int-maker
interface
((ints: [opaque t
        zero: t
        succ:(t -> t)
        pred:(t -> t)
        is-zero:(t -> bool)])
 => [to-int: (from ints take t -> int)])
body
module-proc (ints : [opaque t
        zero:t
        succ:(t -> t)
        pred:(t -> t)
        is-zero: (t -> bool) ])
[to-int =
 let z? = from ints take is-zero
 in let p = from ints take pred
 in letrec int to-int(x: from ints take t) =
  if  (z? x) then 0 else -((to-int (p x)), -1)
 in to-int]
module ints1
interface [
 opaque t
 zero: t
 succ: ( t -> t)
 pred: (t -> t)
 is-zero: (t -> bool) ]
body [
 type t = int
 zero = 0
 succ = proc(x:t) -(x,-1)
 pred = proc(x:t) -(x,1)
 is-zero = proc(x:t) zero?(x) ]
module ints1-to-int
interface [to-int: (from ints1 take t -> int)]
body (to-int-maker ints1)
let i2 = (from ints1 take succ (from ints1 take succ from ints1 take zero))
in (from ints1-to-int take to-int i2)")))
(newline)

(display
 (equal?
  (num-val 3)
  (run "
module maker1
interface
((x:[u:int]) => [v:int])
body
module-proc (x:[u:int])
[v = -(from x take u, -2)]

module maker2
interface
((x:[t:int]) => [u:int])
body
module-proc (x:[t:int])
[u = -(from x take t, -1)]

module m1
interface [t:int]
body [t = 12]

module m2
interface [v:int]
body (maker1 (maker2 m1))

-(from m2 take v, from m1 take t)")))