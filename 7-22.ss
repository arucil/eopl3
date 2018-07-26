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

;;;;;;;;;;;;;;  store  ;;;;;;;;;;;;;;;;

(define the-store 'ha)

(define (empty-store) '#())

(define (init-store)
  (set! the-store (empty-store)))

(define reference? integer?)

(define (vector-clone inc vec)
  (let* ([len (vector-length vec)]
         [v1 (make-vector (+ inc len))])
    (let loop ([i (- len 1)])
      (unless (negative? i)
        (vector-set! v1 i (vector-ref vec i))
        (loop (- i 1))))
    v1))

(define (newref val)
  (let ([len (vector-length the-store)])
    (set! the-store (vector-clone 1 the-store))
    (vector-set! the-store len val)
    len))

(define (deref n)
  (vector-ref the-store n))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                 (format-type (deref (cdar subst))))))

;;;;;;;;;;;;;;;  subst  ;;;;;;;;;;;

(define (apply-one-subst ty0 tvar ty1)
  (cases type ty0
    [proc-type (t0 t1)
               (proc-type (apply-one-subst t0 tvar ty1)
                          (apply-one-subst t1 tvar ty1))]
    [tvar-type (sn)
               (if (equal? ty0 tvar) ty1 ty0)]
    [else ty0]))

(define (need-subst? ty subst)
  (cases type ty
    [proc-type (a b)
               (or (need-subst? a subst)
                   (need-subst? b subst))]
    [tvar-type (s)
               (assoc ty subst)]
    [else #f]))

(define (apply-subst-to-type ty subst)
  (cases type ty
    [proc-type (t0 t1)
               (proc-type (apply-subst-to-type t0 subst)
                          (apply-subst-to-type t1 subst))]
    [tvar-type (sn)
               (let ([tmp (assoc ty subst)])
                 (if tmp
                     (let* ([ref (cdr tmp)]
                            [ty1 (deref ref)])
                       (if (need-subst? ty1 subst)
                           (setref! ref
                                    (apply-subst-to-type ty1 subst))
                           ty1))
                     ty))]
    [else ty]))

(define (empty-subst) '())

(define (extend-subst subst tvar ty)
  (cons (cons tvar (newref ty))
        subst))

;;;;;;;;;;;;;;;;;;;;;;;  unifier  ;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (t s)
  (tvar-type (if (number? s) (string->symbol (number->string s)) s)))
(define f proc-type)
(define int (int-type))
(define bool (bool-type))
(define s 0)
(define (init-subst)
  (set! s (empty-subst)))
(define (add t1 t2)
  (set! s (unifier t1 t2 s (const-exp 1)))
  (format-subst s)
  (newline))

(begin
  (init-store)
  (init-subst)
  (add (t 0) (f (t 'f) (t 1)))
  (add (t 1) (f (t 'x) (t 2)))
  (add (t 3) int)
  (add (t 4) int)
  (add (t 2) int)
  (add (t 'f) (f int (t 3)))
  (add (t 'f) (f (t 'x) (t 4))))