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

    (declaration
     ("opaque" identifier)
     opaque-type-decl)

    (declaration
     ("transparent" identifier "=" type)
     transparent-type-decl)

    (module-body
     ("[" (arbno definition) "]")
     defns-module-body)

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
     ("(" (arbno type) "->" type ")")
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
                  (lookup-var-name-in-decls var-name decls
                                            (lambda ()
                                              (eopl:error 'type-of "variable ~A not bound" var-name)))]))

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
    [extend-tenv-with-module (name i e)
                             (lookup-type-name-in-tenv name e)]
    [extend-tenv-with-type (var val e)
                           (if (equal? var name)
                               val
                               (lookup-type-name-in-tenv name e))]
    ))

(define (lookup-qualified-type-in-tenv m-name t-name tenv)
  (cases interface (lookup-module-name-in-tenv m-name tenv)
    [simple-iface (decls)
                  (lookup-type-name-in-decls t-name decls
                                             (lambda ()
                                               (eopl:error 'type-of "type ~A not bound" t-name)))]))

(define (expand-type ty tenv)
  (cases type ty
    [int-type () ty]
    [bool-type () ty]
    [proc-type (arg-tys ret-ty)
               (proc-type (map (lambda (x)
                                 (expand-type x tenv))
                               arg-tys)
                          (expand-type ret-ty tenv))]
    [named-type (name)
                (expand-type (lookup-type-name-in-tenv name tenv) tenv)]
    [qualified-type (m-name t-name)
                    (lookup-qualified-type-in-tenv m-name t-name tenv)]))

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
    [proc-exp (vars arg-types exp1)
              (proc-val (procedure vars exp1 env))]
    
    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]
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
                                  (extend-env var val env))))]
        [else
         (defns-to-env (cdr defns) env)]
        )))

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
                                   (add-module-defns-to-tenv
                                    (cdr defns)
                                    (extend-tenv-with-module
                                     m-name
                                     (expand-iface m-name expected-iface tenv)
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
                            (extend-tenv var-name ty tenv))))]
        [type-defn (name ty)
                   (cons (transparent-type-decl name ty)
                         (defns-to-decls
                           (cdr defns)
                           (extend-tenv-with-type name ty tenv)))]
        )))

(define (expand-iface m-name iface tenv)
  (cases interface iface
    [simple-iface (decls)
                  (simple-iface (expand-decls m-name decls tenv))]))

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
                               (cons
                                (transparent-type-decl t-name ty)
                                (expand-decls m-name
                                              (cdr decls)
                                              (extend-tenv-with-type
                                               t-name ty internal-tenv)))]
        [val-decl (name ty)
                  (cons (val-decl name
                                  (let rec ([ty ty])
                                    (cases type ty
                                      [proc-type (arg-tys ret-ty)
                                                 (proc-type (map rec arg-tys)
                                                            (rec ret-ty))]
                                      [named-type (name)
                                                  (qualified-type m-name name)]
                                      [else ty])))
                        (expand-decls
                         m-name
                         (cdr decls)
                         internal-tenv))])))

(define (<:-iface iface1 iface2 tenv)
  (cases interface iface1
    [simple-iface (decls1)
                  (cases interface iface2
                    [simple-iface (decls2)
                                  (<:-decls decls1 decls2
                                            (extend-tenv-with-decls decls1 tenv))])]))

(define (<:-decls decls1 decls2 tenv)
  (if (null? decls2)
      #t
      (and (<:-decl decls1 (car decls2) tenv)
           (<:-decls decls1 (cdr decls2) tenv))))

(define (extend-tenv-with-decl decl tenv)
  (cases declaration decl
    [val-decl (a b) tenv]
    [transparent-type-decl (name ty)
                           (extend-tenv-with-type name ty tenv)]
    [opaque-type-decl (name)
                      (eopl:error 'extend-tenv-with-decl
                                  "unreachable opaque ~A"
                                  name)]))

(define (extend-tenv-with-decls decls tenv)
  (if (null? decls)
      tenv
      (extend-tenv-with-decls (cdr decls)
                              (extend-tenv-with-decl (car decls)
                                                     tenv))))

(define (<:-decl decls1 decl2 tenv)
  (cases declaration decl2
    [val-decl (var ty)
              (let ([ty1 (lookup-var-name-in-decls var decls1 (lambda () #f))])
                (and ty1
                     (equiv-type? ty1
                                  ty
                                  tenv)))]
    [transparent-type-decl (name ty)
                           (let ([ty1 (lookup-type-name-in-decls name decls1 (lambda () #f))])
                             (and ty1
                                  (equiv-type? ty1
                                               ty
                                               tenv)))]
    [opaque-type-decl (name)
                      (lookup-type-name-in-decls name decls1 (lambda () #f))]))

(define (equiv-type? ty1 ty2 tenv)
  (equal? (expand-type ty1 tenv)
          (expand-type ty2 tenv)))

(define (lookup-var-name-in-decls var-name decls f)
  (if (null? decls)
      (f)
      (cases declaration (car decls)
        [val-decl (var type)
                  (if (eqv? var var-name)
                      type
                      (lookup-var-name-in-decls var-name (cdr decls) f))]
        [else
         (lookup-var-name-in-decls var-name (cdr decls) f)]
        )))

(define (lookup-type-name-in-decls var-name decls f)
  (if (null? decls)
      (f)
      (cases declaration (car decls)
        [val-decl (var type)
                  (if (eqv? var var-name)
                      type
                      (lookup-type-name-in-decls var-name (cdr decls) f))]
        [transparent-type-decl (name type)
                               (if (eqv? name var-name)
                                   type
                                   (lookup-type-name-in-decls var-name (cdr decls) f))]
        [else
         (eopl:error lookup-type-name-in-decls
                     "unreachable ~A"
                     var-name)]
        )))

(define (check-equal-type! ty1 ty2 tenv exp)
  (unless (equiv-type? ty1 ty2 tenv)
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
              (check-equal-type! (type-of exp1 tenv) (int-type) tenv exp1)
              (check-equal-type! (type-of exp2 tenv) (int-type) tenv exp2)
              (int-type)]
    [zero?-exp (exp1)
               (check-equal-type! (type-of exp1 tenv) (int-type) tenv exp1)
               (bool-type)]
    [if-exp (exp1 exp2 exp3)
            (let ([ty1 (type-of exp2 tenv)])
              (check-equal-type! (type-of exp1 tenv)
                                 (bool-type)
                                 tenv exp1)
              (check-equal-type! ty1
                                 (type-of exp3 tenv)
                                 tenv exp)
              ty1)]
    [let-exp (vars exps body)
             (let loop ([vars vars]
                        [exps exps]
                        [tenv1 tenv])
               (if (null? vars)
                   (type-of body tenv1)
                   (loop (cdr vars)
                         (cdr exps)
                         (extend-tenv (car vars)
                                      (type-of (car exps) tenv)
                                      tenv1))))]
    [proc-exp (vars arg-types body)
              (proc-type arg-types
                          (type-of body
                                   (extend-tenv* vars arg-types tenv)))]
    [call-exp (exp1 exps)
              (let ([ty1 (expand-type (type-of exp1 tenv) tenv)])
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
                                                    tenv
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
                                         tenv
                                         (car bodies))))
                  (type-of exp1 tenv1))]
    [qualified-var-exp (m-name var)
                       (lookup-qualified-var-in-tenv m-name var tenv)]
    ))

(eopl:pretty-print
 (run "
module ints
interface [
 opaque t
 zero: t
 succ: (t -> t)
 pred: (t -> t)
 is-zero: (t -> bool)
 sub: (t t -> t)
]
body [
 type t = int
 zero = 0
 succ = proc(x:t) -(x,-1)
 pred = proc(x:t) -(x,1)
 is-zero = proc(x:t) zero?(x)
 sub = proc(x:t, y:t) -(x,y)
]
module table
interface [
 opaque table
 transparent t = from ints take t
 transparent t1 = t
 empty: table
 add-to-table: (t int table -> table)
 lookup-in-table: (t table -> int)
]
body [
 type t = from ints take t
 type t1 = from ints take t
 type table = (t -> int)
 empty = proc (x: t) 0
 z? = from ints take is-zero
 sub = from ints take sub
 add-to-table = proc(var: t, val: int, t: table)
                 proc(x: t)
                  if (z? (sub var x))
                  then val
                  else (t x)
 lookup-in-table = proc(var:t, t:table)
                    (t var)
]
let empty = from table take empty
    add-binding = from table take add-to-table
    lookup = from table take lookup-in-table
    z = from ints take zero
    s = from ints take succ
    p = from ints take pred
    z? = from ints take is-zero
in let i3 = (s (s (s z)))
       i4 = (s (s (s (s z))))
in let t1 = (add-binding i3 300
             (add-binding i4 400
              (add-binding i3 500
               empty)))
in -((lookup i4 t1), (lookup i3 t1))"))