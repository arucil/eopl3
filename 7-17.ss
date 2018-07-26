#lang eopl

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
     (type)
     a-type)

    (optional-type
     ("?")
     no-type)

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
     ("%tvar-type" identifier)
     tvar-type)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (format-type ty)
  (cases type ty
    [int-type () 'int]
    [bool-type () 'bool]
    [proc-type (ty0 ty1)
               (list (format-type ty0)
                     '->
                     (format-type ty1))]
    [tvar-type (sn)
               (string->symbol (string-append "t_" (symbol->string sn)))]))

(define (format-subst subst)
  (unless (null? subst)
    (format-subst (cdr subst))
    (eopl:printf "~A = ~A~%"
                 (format-type (caar subst))
                 (format-type (cdar subst)))))


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
                     (apply-subst-to-type (cdr tmp) subst)
                     ty))]
    [else ty]))

(define (empty-subst) '())

(define (extend-subst tvar ty subst)
  (cons (cons tvar ty)
        subst))

(define (t s)
  (tvar-type (if (number? s) (string->symbol (number->string s)) s)))
(define f proc-type)
(define int (int-type))
(define bool (bool-type))
(define s (extend-subst (t 'f) (f int (t 3))
                        (extend-subst (t 2) int
                                      (extend-subst (t 4) int
                                                    (extend-subst (t 3) int
                                                                  (extend-subst (t 1) (f (t 'x) (t 2))
                                                                                (extend-subst (t 0)
                                                                                              (f (t 'f) (t 1))
                                                                                              (empty-subst))))))))