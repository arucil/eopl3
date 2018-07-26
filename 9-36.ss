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
  '((program ((arbno class-decl) expression) a-program)

    (class-decl
     ("class" identifier "extends" identifier (arbno "implements" identifier)
              (arbno "field" type identifier) (arbno method-decl))
     a-class-decl)

    (method-decl
     ("method" type identifier "(" (separated-list identifier ":" type ",") ")" expression)
     a-method-decl)

    (class-decl
     ("interface" identifier (arbno "extends" identifier) (arbno abstract-method-decl))
     an-interface-decl)

    (abstract-method-decl
     ("method" type identifier "(" (separated-list identifier ":" type ",") ")")
     an-abstract-method-decl)
    
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
     ("letrec" (arbno type identifier "(" (separated-list identifier ":" type ",") ")" "=" expression) "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ":" type ",") ")" expression)
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
     ("list" "(" expression (arbno "," expression) ")")
     list-exp)

    (expression
     ("new" identifier "(" (separated-list expression ",") ")")
     new-object-exp)

    (expression
     ("send" expression identifier "(" (separated-list expression ",") ")")
     method-call-exp)

    (expression
     ("super" identifier "(" (separated-list expression ",") ")")
     super-call-exp)

    (expression
     ("self")
     self-exp)

    (expression
     ("cast" expression identifier)
     cast-exp)

    (expression
     ("instanceof" expression identifier)
     instanceof-exp)

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
     ("listof" type)
     list-type)

    (type
     ("void")
     void-type)

    (type
     (identifier)
     class-type)
    
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
   (env environment?))
  (extend-env-with-self-and-super
   (self object?)
   (super identifier?)
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
    [extend-env-with-self-and-super (self super e)
                                    (cond
                                      [(eqv? svar '%self)
                                       self]
                                      [(eqv? svar '%super)
                                       super]
                                      [else
                                       (apply-env e svar)])]
    ))

;;;;;;;;;;;;;; class env  ;;;;;;;;;;;;

(define the-class-env 'ha)

(define (add-to-class-env! c-name c)
  (set! the-class-env
        (cons (cons c-name c)
              the-class-env)))

(define (lookup-class name)
  (let ([p (assq name the-class-env)])
    (if p
        (cdr p)
        (eopl:error 'lookup-class
                    "unknown class ~A"
                    name))))

(define (init-class-env! c-decls)
  (set! the-class-env (list (cons 'object (a-class #f '() '()))))
  (for-each init-class-decl! c-decls))

(define (init-class-decl! c-decl)
  (cases class-decl c-decl
    [a-class-decl (c-name s-name i-names f-types f-names m-decls)
                  (let ([f-names (append-field-names (class->field-names (lookup-class s-name))
                                                     f-names)])
                    (add-to-class-env! c-name
                                       (a-class s-name f-names
                                                (merge-method-envs
                                                 (class->method-env (lookup-class s-name))
                                                 (method-decls->method-env
                                                  m-decls s-name f-names)))))]
    [an-interface-decl (i-name s-names am-decls)
                       1]
    ))

(define (append-field-names s-fields new-fields)
  (if (null? s-fields)
      new-fields
      (cons (if (memq (car s-fields) new-fields)
                (new-identifier (car s-fields))
                (car s-fields))
            (append-field-names (cdr s-fields)
                                new-fields))))

(define new-identifier
  (let ([i 0])
    (lambda (p)
      (set! i (+ i 1))
      (string->symbol
       (string-append
        (symbol->string p)
        (number->string i))))))

(define-datatype class class?
  [a-class
   (super-name (maybe identifier?))
   (field-names (list-of identifier?))
   (method-env method-environment?)])

(define (class->field-names c)
  (cases class c
    [a-class (s-name f-names m-env)
             f-names]))

(define (class->super-name c)
  (cases class c
    [a-class (s-name f-names m-env)
             s-name]))

(define (class->method-env c)
  (cases class c
    [a-class (s-name f-names m-env)
             m-env]))

(define (find-method c-name name)
  (let ([p (assq name (class->method-env (lookup-class c-name)))])
    (if p
        (cdr p)
        (eopl:error 'find-method
                    "method ~A not found in class ~A"
                    name c-name))))

(define (method-decls->method-env m-decls s-name f-names)
  (map (lambda (m-decl)
         (cases method-decl m-decl
           [a-method-decl (m-type m-name vars tys body)
                          (cons m-name
                                (a-method vars body s-name f-names))]))
       m-decls))

(define (merge-method-envs s-m-env new-m-env)
  (append new-m-env s-m-env))

(define method-environment? (list-of pair?))

(define-datatype object object?
  [an-object
   (class-name identifier?)
   (fields (list-of reference?))])

(define-datatype method method?
  [a-method
   (vars (list-of identifier?))
   (body expression?)
   (super-name identifier?)
   (field-names (list-of identifier?))])

(define (object->class-name obj)
  (cases object obj
    [an-object (name ls)
               name]))

(define (object->fields obj)
  (cases object obj
    [an-object (name ls)
               ls]))

;;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (b-vars (list-of identifier?))
   (body expression?)
   (env environment?)))

(define (apply-procedure p refs)
  (cases proc p
    [procedure (vars body env)
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
  (list-val
   (ls (list-of expval?))))

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

(define (expval->list val)
  (cases expval val
    [list-val (proc) proc]
    [else
     (eopl:error 'expval->list "expval ~A is not list" val)]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (let ([pgm (scan&parse prog)])
    (type-of-program pgm)
    (cases program pgm
      [a-program (class-decls exp)
                 (init-store)
                 (init-class-env! class-decls)
                 (value-of exp (empty-env))])))

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
    [letrec-exp (p-tys p-names b-varss b-tyss bodies exp)
                (value-of exp (extend-env-rec p-names b-varss bodies env))]

    ;;; procedures
    [proc-exp (vars tys exp)
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
               (let rec ([val (value-of exp1 env)])
                 (cases expval val
                   [num-val (num)
                            (display num)]
                   [bool-val (bool)
                             (display bool)]
                   [proc-val (proc)
                             (display "#procedure")]
                   [list-val (ls)
                             (display "(")
                             (let loop ([ls ls])
                               (unless (null? ls)
                                 (rec (car ls))
                                 (unless (null? (cdr ls))
                                   (display " "))
                                 (loop (cdr ls))))
                             (display ")")]
                   ))
               (newline)
               (num-val 1)]
    [list-exp (exp1 exps)
              (list-val (values-of-exps
                         (cons exp1 exps)
                         env))]

    [self-exp ()
              (apply-env env '%self)]
    [method-call-exp (obj-exp m-name rands)
                     (let ([obj (value-of obj-exp env)])
                       (apply-method
                        (find-method (object->class-name obj)
                                     m-name)
                        obj
                        (values-of-exps rands env)))]
    [super-call-exp (m-name rands)
                    (apply-method (find-method (apply-env env '%super) m-name)
                                  (apply-env env '%self)
                                  (values-of-exps rands env))]
    [new-object-exp (c-name rands)
                    (let ([obj (new-object c-name)])
                      (apply-method (find-method c-name 'initialize)
                                    obj
                                    (values-of-exps rands env))
                      obj)]
    [cast-exp (exp1 c-name)
              (let ([obj (value-of exp1 env)])
                (if (is-subclass? (object->class-name obj)
                                  c-name)
                    obj
                    (eopl:error 'value-of
                                "~A cannot be cast into ~A"
                                obj
                                c-name)))]
    [instanceof-exp (exp1 c-name)
                    (let ([obj (value-of exp1 env)])
                      (bool-val (is-subclass? (object->class-name obj)
                                              c-name)))]
    ))

(define (is-subclass? c-name1 c-name2)
  (if (eqv? c-name1 c-name2)
      #t
      (let ([s-name (class->super-name (lookup-class c-name1))])
        (if s-name
            (is-subclass? s-name c-name2)
            #f))))

(define (values-of-exps exps env)
  (if (null? exps)
      '()
      (cons (value-of (car exps) env)
            (values-of-exps (cdr exps) env))))

(define (new-object c-name)
  (an-object c-name
             (map (lambda (f-name)
                    (newref (list 'uninitialized f-name)))
                  (class->field-names (lookup-class c-name)))))

(define (apply-method m self args)
  (cases method m
    [a-method (vars body super-name field-names)
              (value-of body
                        (extend-env* vars
                                     (map newref args)
                                     (extend-env-with-self-and-super
                                      self
                                      super-name
                                      (extend-env* field-names
                                                   (object->fields self)
                                                   (empty-env)))))]))

;;;;;;;;;;;;;;;;  static env  ;;;;;;;;;;;;;;;

(define (empty-tenv) '())

(define (extend-tenv var ty tenv)
  (cons (cons var ty)
        tenv))

(define (apply-tenv tenv var)
  (let ([p (assv var tenv)])
    (if p
        (cdr p)
        (eopl:error 'type-of
                    "variable ~A not bound"
                    var))))

(define (extend-tenv* vars tys tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars)
                    (cdr tys)
                    (extend-tenv (car vars)
                                 (car tys)
                                 tenv))))

(define-datatype static-class static-class?
  [a-static-class
   (s-name (maybe identifier?))
   (i-names (list-of identifier?))
   (f-names (list-of identifier?))
   (f-types (list-of type?))
   (m-tenv method-tenv?)]
  [an-interface
   (m-tenv method-tenv?)])

(define (static-class->interface-names sc)
  (cases static-class sc
    [a-static-class (s-name i-names f-names f-types m-tenv)
                    i-names]
    [an-interface (m-tenv)
                  (eopl:error 'type-of
                              "unreachable ~A"
                              sc)]))

(define (static-class->field-names sc)
  (cases static-class sc
    [a-static-class (s-name i-names f-names f-types m-tenv)
                    f-names]
    [an-interface (m-tenv)
                  (eopl:error 'type-of
                              "unreachable ~A"
                              sc)]))

(define (static-class->method-tenv sc)
  (cases static-class sc
    [a-static-class (s-name i-names f-names f-types m-tenv)
                    m-tenv]
    [an-interface (m-tenv)
                  m-tenv]))

(define (static-class->field-types sc)
  (cases static-class sc
    [a-static-class (s-name i-names f-names f-types m-tenv)
                    f-types]
    [an-interface (m-tenv)
                  (eopl:error 'type-of
                              "unreachable ~A"
                              sc)]))

(define (static-class->super-name sc)
  (cases static-class sc
    [a-static-class (s-name i-names f-names f-types m-tenv)
                    s-name]
    [an-interface (m-tenv)
                  #f]))

(define method-tenv? (list-of pair?))

(define the-static-class-env 'a)

(define (empty-the-static-class-env!)
  (set! the-static-class-env '()))

(define (init-static-class-env! c-decls)
  (empty-the-static-class-env!)
  (add-static-class-binding! 'object
                             (a-static-class #f '() '() '() '()))
  (for-each add-class-decl-to-static-class-env! c-decls))

(define (add-static-class-binding! name c)
  (set! the-static-class-env
        (cons (cons name c)
              the-static-class-env)))

(define (add-class-decl-to-static-class-env! c-decl)
  (cases class-decl c-decl
    [an-interface-decl (i-name s-names abs-m-decls)
                       (let ([m-tenv (abs-method-decls->method-tenv abs-m-decls)]
                             [s-m-tenv (apply merge-abs-method-tenvs
                                              (map (lambda (s-name)
                                                     (cases static-class (lookup-static-class s-name)
                                                       [an-interface (m-tenv)
                                                                     m-tenv]
                                                       [a-static-class (a b c d e)
                                                                       (eopl:error
                                                                        'type-of
                                                                        "interface ~A extends from non-interface ~A"
                                                                        i-name s-name)]))
                                                   s-names))])
                         (check-no-dups! (map car m-tenv) i-name)
                         (add-static-class-binding!
                          i-name
                          (an-interface
                           (merge-abs-method-tenvs m-tenv s-m-tenv))))]
    [a-class-decl (c-name s-name i-names f-types f-names m-decls)
                  (let* ([s-class (lookup-static-class s-name)]
                         [i-names (append
                                   (static-class->interface-names s-class)
                                   i-names)]
                         [f-names (append-field-names
                                   (static-class->field-names s-class)
                                   f-names)]
                         [m-tenv (let ([new-m-tenv (method-decls->method-tenv m-decls)])
                                        (check-no-dups! (map car new-m-tenv) c-name)
                                        (merge-method-tenvs
                                         (static-class->method-tenv s-class)
                                         new-m-tenv))])
                    (check-no-dups! i-names c-name)
                    (check-no-dups! f-names c-name)
                    (check-for-initialize! m-tenv c-name)
                    (add-static-class-binding! c-name
                                               (a-static-class s-name
                                                               i-names
                                                               f-names
                                                               (append
                                                                (static-class->field-types s-class)
                                                                f-types)
                                                               m-tenv)))]))

(define (abs-method-decls->method-tenv m-decls)
  (if (null? m-decls)
      '()
      (cases abstract-method-decl (car m-decls)
        [an-abstract-method-decl (ty m-name args arg-tys)
                                 (cons (cons m-name
                                             (proc-type arg-tys ty))
                                       (abs-method-decls->method-tenv (cdr m-decls)))])))

(define (method-decls->method-tenv m-decls)
  (if (null? m-decls)
      '()
      (cases method-decl (car m-decls)
        [a-method-decl (ty m-name args arg-tys body)
                                 (cons (cons m-name
                                             (proc-type arg-tys ty))
                                       (method-decls->method-tenv (cdr m-decls)))])))

(define (merge-method-tenvs s-m-tenv new-m-tenv)
  (append new-m-tenv s-m-tenv))

(define (merge-abs-method-tenvs . tenvs)
  (apply append tenvs))

(define (check-no-dups! ls c-name)
  (unless (null? ls)
    (if (memv (car ls) (cdr ls))
        (eopl:error 'type-of
                    "duplicate ~A in ~A, class ~A"
                    (car ls)
                    ls
                    c-name)
        (check-no-dups! (cdr ls) c-name))))

(define (check-for-initialize! m-tenv c-name)
  (unless (assv 'initialize m-tenv)
    (eopl:error 'type-of
                "class ~A has no initialize method"
                c-name)))

(define (lookup-static-class c-name)
  (let ([p (assv c-name the-static-class-env)])
    (if p
        (cdr p)
        (eopl:error 'type-of
                    "class ~A not found"
                    c-name))))

(define (check-class-decl! c-decl)
  (cases class-decl c-decl
    [an-interface-decl (a b c) #t]
    [a-class-decl (c-name s-name i-names f-types f-names m-decls)
                  (let ([sc (lookup-static-class c-name)])
                    (for-each (lambda (m-decl)
                                (check-method-decl! m-decl
                                                    c-name
                                                    s-name
                                                    (static-class->field-names sc)
                                                    (static-class->field-types sc)))
                              m-decls)
                    (for-each (lambda (i-name)
                                (check-if-implements! c-name i-name))
                              i-names))]))

(define (check-method-decl! m-decl c-name s-name f-names f-types)
  (cases method-decl m-decl
    [a-method-decl (ret-type m-name vars var-tys body)
                   (check-is-subtype!
                    (type-of
                     body
                     (extend-tenv*
                      vars var-tys
                      (extend-tenv*
                       '(%self %super %method)
                       (list (class-type c-name)
                             s-name
                             m-name)
                       (extend-tenv*
                        f-names f-types
                        (empty-tenv)))))
                    ret-type m-decl)
                   (if (eqv? m-name 'initialize)
                       #t
                       (let ([s-type (maybe-find-method-type
                                      (static-class->method-tenv
                                       (lookup-static-class s-name))
                                      m-name)])
                         (if s-type
                             (check-is-subtype!
                              (proc-type var-tys ret-type)
                              s-type body)
                             #t)))]))

(define (check-if-implements! c-name i-name)
  (cases static-class (lookup-static-class i-name)
    [a-static-class (a b c d e)
                    (eopl:error 'type-of
                                "~A cannot implement non-interface ~A"
                                c-name i-name)]
    [an-interface (m-tenv)
                  (let ([c-m-tenv (static-class->method-tenv (lookup-static-class c-name))])
                    (for-each (lambda (m-b)
                                (let* ([m-name (car m-b)]
                                       [c-m-type (maybe-find-method-type c-m-tenv m-name)])
                                  (if c-m-type
                                      (check-is-subtype! c-m-type
                                                         (cdr m-b)
                                                         c-name)
                                      (eopl:error 'type-of
                                                  "class ~A missing method ~A for interface ~A"
                                                  c-name m-name i-name))))
                              m-tenv))]))

(define (maybe-find-method-type m-tenv m-name)
  (let ([p (assv m-name m-tenv)])
    (if p (cdr p) #f)))

(define (find-method-type c-name m-name)
  (let ([p (assv m-name (static-class->method-tenv (lookup-static-class c-name)))])
    (if p
        (cdr p)
        (eopl:error 'type-of
                    "method ~A not found"
                    m-name))))

(define (current-method tenv)
  (let ([p (assv '%method tenv)])
    (if p
        (cdr p)
        #f)))

;;;;;;;;;;;;;;;;;  type checker  ;;;;;;;;;;;;;;;

(define (type-of-program pgm)
  (cases program pgm
    [a-program (c-decls exp1)
               (init-static-class-env! c-decls)
               (for-each check-class-decl! c-decls)
               (type-of exp1 (empty-tenv))]))

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
    [plus-exp (exp1 exp2)
              (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
              (check-equal-type! (type-of exp2 tenv) (int-type) exp2)
              (int-type)]
    [equal?-exp (exp1 exp2)
              (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
              (check-equal-type! (type-of exp2 tenv) (int-type) exp2)
              (bool-type)]
    [assign-exp (var exp1)
                (apply-tenv tenv var)
                (type-of exp1 tenv)
                (void-type)]
    [begin-exp (exp1 exps)
               (let loop ([ty (type-of exp1 tenv)]
                          [exps exps])
                 (if (null? exps)
                     ty
                     (loop (type-of (car exps) tenv)
                           (cdr exps))))]
    [zero?-exp (exp1)
               (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
               (bool-type)]
    [print-exp (exp1)
               (check-equal-type! (type-of exp1 tenv) (int-type) exp1)
               (void-type)]
    [if-exp (exp1 exp2 exp3)
            (let ([ty1 (type-of exp2 tenv)])
              (check-equal-type! (type-of exp1 tenv)
                                 (bool-type)
                                 exp1)
              (check-is-subtype! ty1
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
              (type-of-call (type-of exp1 tenv)
                            (types-of-exps exps tenv)
                            exps
                            exp)]
    [letrec-exp (ret-tys names varss arg-tyss bodies exp1)
                (let ([tenv1 (extend-tenv* names
                                           (map proc-type arg-tyss ret-tys)
                                           tenv)])
                  (for-each (lambda (body ret-ty vars arg-tys)
                              (check-is-subtype! (type-of body
                                                          (extend-tenv* vars
                                                                        arg-tys
                                                                        tenv1))
                                                 ret-ty
                                                 body))
                            bodies ret-tys varss arg-tyss)
                  (type-of exp1 tenv1))]
    [list-exp (exp1 exps)
              (let ([ty1 (type-of exp1 tenv)])
                (for-each (lambda (x)
                            (check-equal-type! ty1
                                               (type-of x tenv)
                                               x))
                          exps)
                (list-type ty1))]
    [self-exp ()
              (apply-tenv tenv '%self)]
    [instanceof-exp (exp1 c-name)
                    (let ([ty (type-of exp1 tenv)])
                      (if (and (class-type? ty)
                               (let ([c-name0 (type->class-name ty)])
                                 (and (is-static-class-or-interface? c-name0)
                                      (is-static-class? c-name)
                                      (or (statically-is-subclass? c-name c-name0)
                                          (and (is-static-class? c-name0)
                                               (statically-is-subclass? c-name0 c-name))))))
                          (bool-type)
                          (eopl:error 'type-of
                                      "bad type ~A to instanceof ~A in ~A"
                                      (format-type ty)
                                      c-name
                                      exp1)))]
    [cast-exp (exp1 c-name)
              (let ([ty (type-of exp1 tenv)])
                (if (and (class-type? ty)
                         (let ([c-name0 (type->class-name ty)])
                           (and (is-static-class-or-interface? c-name0)
                                (is-static-class? c-name)
                                (or (statically-is-subclass? c-name c-name0)
                                    (and (is-static-class? c-name0)
                                         (statically-is-subclass? c-name0 c-name))))))
                    (class-type c-name)
                    (eopl:error 'type-of
                                "bad type ~A to cast ~A in ~A"
                                (format-type ty)
                                c-name
                                exp1)))]
    [method-call-exp (exp1 m-name exps)
                     (when (eqv? m-name 'initialize)
                       (eopl:error 'type-of
                                   "invalid initialize call in ~A"
                                   exp))
                     (type-of-call (find-method-type
                                    (type->class-name
                                     (type-of exp1 tenv))
                                    m-name)
                                   (types-of-exps exps tenv)
                                   exps
                                   exp)]
    [super-call-exp (m-name exps)
                    (when (eqv? m-name 'initialize)
                      (unless (eqv? 'initialize
                                    (current-method tenv))
                        (eopl:error 'type-of
                                    "invalid initialize call in ~A"
                                    exp)))
                    (type-of-call (find-method-type
                                   (apply-tenv tenv '%super)
                                   m-name)
                                  (types-of-exps exps tenv)
                                  exps
                                  exp)]
    [new-object-exp (c-name exps)
                    (cases static-class (lookup-static-class c-name)
                      [an-interface (m-tenv)
                                    (eopl:error 'type-of
                                                "cannot instantiate interface ~A" c-name)]
                      [a-static-class (s-name i-names f-names f-types m-tenv)
                                      (type-of-call (find-method-type c-name 'initialize)
                                                    (types-of-exps exps tenv)
                                                    exps
                                                    exp)
                                      (class-type c-name)])]
    ))
  
(define (class-type? ty)
  (cases type ty
    [class-type (n) #t]
    [else #f]))

(define (type->class-name ty)
  (cases type ty
    [class-type (n) n]
    [else
     (eopl:error 'type-of
                 "type ~A is not class"
                 (format-type ty))]))

(define (is-static-class-or-interface? c-name)
  (assv c-name the-static-class-env))

(define (is-static-class? c-name)
  (let ([p (assv c-name the-static-class-env)])
    (if p
        (cases static-class (cdr p)
          [a-static-class (a b c d e)
                          #t]
          [else #f])
        #f)))

(define (static-class-is-class? c-name)
  (cases static-class (lookup-static-class c-name)
    [a-static-class (a b c d e) #t]
    [else #f]))

(define (types-of-exps exps tenv)
  (map (lambda (x)
         (type-of x tenv))
       exps))

(define (type-of-call ty1 tys exps exp)
  (cases type ty1
    [proc-type (arg-tys ret-ty)
               (unless (= (length arg-tys)
                          (length tys))
                 (eopl:error 'type-of
                             "argument number mismatch, expecting ~A, got ~A in ~A"
                             (length arg-tys)
                             (length tys)
                             exp))
               (for-each check-is-subtype! tys arg-tys exps)
               ret-ty]
    [else
     (eopl:error 'type-of "operator is ~A rather than proc" (format-type ty1))]))

(define (check-is-subtype! ty1 ty2 exp)
  (unless (is-subtype? ty1 ty2)
    (eopl:error 'type-of
                "~A is not subtype of ~A in ~A"
                (format-type ty1)
                (format-type ty2)
                exp)))

(define (check-equal-type! ty1 ty2 exp)
  (unless (equal? ty1 ty2)
    (eopl:error 'type-of
                "types mismatch: ~A != ~A in ~A"
                (format-type ty1)
                (format-type ty2)
                exp)))

(define (is-subtype? ty1 ty2)
  (cases type ty1
    [class-type (name1)
                (cases type ty2
                  [class-type (name2)
                              (statically-is-subclass? name1 name2)]
                  [else #f])]
    [proc-type (args1 res1)
               (cases type ty2
                 [proc-type (args2 res2)
                            (and (every2? is-subtype? args2 args1)
                                 (is-subtype? res1 res2))]
                 [else #f])]
    [else (equal? ty1 ty2)]))

(define (statically-is-subclass? name1 name2)
  (or (eqv? name1 name2)
      (let ([s-name (static-class->super-name (lookup-static-class name1))])
        (if s-name
            (statically-is-subclass? s-name name2)
            #f))
      (memv name2
            (static-class->interface-names
             (lookup-static-class name1)))))

(define (every2? pred ls1 ls2)
  (cond
    [(null? ls1)
     (null? ls2)]
    [(null? ls2)
     #f]
    [(pred (car ls1) (car ls2))
     (every2? pred (cdr ls1) (cdr ls2))]
    [else #f]))

(define (format-type ty)
  (cases type ty
    [int-type () 'int]
    [bool-type () 'bool]
    [proc-type (argtys retty)
               (append (map format-type argtys)
                       (list '->
                             (format-type retty)))]
    [class-type (c-name)
                c-name]
    [list-type (ty)
               (list 'listof
                     (format-type ty))]
    [void-type ()
               'void]
    ))

;;;;;;;;;;;; ;;;;;;;;;;;;;  test ;;;;;;;;;;;;;;;;;;;;

(define (to-expval a)
  (cond
    [(list? a)
     (list-val (map to-expval a))]
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

(test '((3 -3)
        (5 -5))
      "
class c1 extends object
 field int i
 field int j
 method void initialize (x:int)
 begin
  set i = x;
  set j = -(0,x);
 end
 method void countup(d:int)
 begin
  set i = +(i,d);
  set j = -(j,d);
 end
 method listof int get() list(i,j)

let t1 = 0
 t2 = 0
 o1 = new c1(3)
in begin
 set t1 = send o1 get();
 send o1 countup(2);
 set t2 = send o1 get();
 list(t1, t2);
end")

(test '(101 102 101 999)
      "
class c1 extends object
 field int x
 field int y
 method int initialize() 1
 method void setx1(v:int) set x = v
 method void sety1(v:int) set y = v
 method int getx1() x
 method int gety1() y
class c2 extends c1
 field int y
 method void sety2(v:int) set y = v
 method int getx2() x
 method int gety2() y
let o2 = new c2()
in begin
 send o2 setx1(101);
 send o2 sety1(102);
 send o2 sety2(999);
 list(send o2 getx1(),
      send o2 gety1(),
      send o2 getx2(),
      send o2 gety2());
end")

(test '(11 22 22)
      "
class c1 extends object
 method int initialize() 1
 method int m1() 11
 method int m2() send self m1()
class c2 extends c1
 method int m1() 22
list(send new c1() m1(),
     send new c2() m1(),
     send new c2() m2())
")

(test '(23 33)
      "
class c1 extends object
 method int initialize() 1
 method int m1() send self m2()
 method int m2() 13
class c2 extends c1
 method int m1() 22
 method int m2() 23
 method int m3() super m1()
class c3 extends c2
 method int m1() 32
 method int m2() 33
list(send new c2() m3(),
     send new c3() m3())
")

(test '(12 12 100 200)
      "
interface tree
 method int sum()
 method bool equal(t:tree)

class node extends object implements tree
 field tree left
 field tree right
 method void initialize(l:tree, r:tree)
  begin
   set left = l;
   set right = r;
  end
 method tree left() left
 method tree right() right
 method int sum() +(send left sum(), send right sum())
 method bool equal(t:tree)
  if instanceof t node
  then if send left equal(send cast t node left())
       then send right equal(send cast t node right())
       else zero?(1)
  else zero?(1)

class leaf extends object implements tree
 field int value
 method void initialize(v:int) set value = v
 method int sum() value
 method int value() value
 method bool equal(t:tree)
  if instanceof t leaf
  then equal?(value, send cast t leaf value())
  else zero?(1)

let o1 = new node(
         new node(
          new leaf(3),
          new leaf(4)),
         new leaf(5))
    o2 = new node(
          new node(
           new node(
            new leaf(1),
            new leaf(2)),
           new leaf(4)),
          new leaf(5))
in list(send o1 sum(),
        send o2 sum(),
        if send o1 equal(o1) then 100 else 200,
        if send o1 equal(o2) then 100 else 200)
")

(test 1
      "
class c1 extends object
 method int initialize() 1

class c2 extends c1

class c3 extends c2

interface i1
 method c2 m1(x:c2)

interface i2 extends i1
 method int m2()

interface i3 extends i2
 method c2 m1(x:c1)

interface i4 extends i2
 method c3 m1(x:c2)

interface i5
 method int m3()

interface i6 extends i4 extends i5

class c4 extends object implements i4 implements i6
 method int initialize() 1
 method c3 m1(x:c1) new c3()
 method int m2() 1
 method int m3() 1
1")