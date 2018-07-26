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
     ("class" identifier "extends" identifier (arbno field-decl) (arbno method-decl))
     a-class-decl)

    (field-decl
     ("field" accessibility identifier)
     a-field-decl)

    (method-decl
     ("method" accessibility identifier "(" (separated-list identifier ",") ")" expression)
     a-method-decl)

    (accessibility
     ("public")
     public-acc)

    (accessibility
     ("protected")
     protected-acc)

    (accessibility
     ("private")
     private-acc)
    
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
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    (expression
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
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
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    (expression
     ("null")
     null-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

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
     ("fieldref" expression identifier)
     fieldref-exp)

    (expression
     ("fieldset" expression identifier "=" expression)
     fieldset-exp)
    
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

(define (location sym list . args)
  (let ([eq (if (null? args)
                eqv?
                (car args))])
    (let loop ([ls list]
               [n 0])
      (cond
        [(null? ls) #f]
        [(eq sym (car ls)) n]
        [else
         (loop (cdr ls) (+ n 1))]))))

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

(define (current-self env)
  (cases environment env
    [empty-env () #f]
    [extend-env (a b e)
                (current-self e)]
    [extend-env-rec (a b c e)
                    (current-self e)]
    [extend-env-with-self-and-super (self b e)
                                    self]))

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
    [a-class-decl (c-name s-name f-decls m-decls)
                  (let ([f-env (append-field-env (class->field-env (lookup-class s-name))
                                                 (field-decls->field-env c-name f-decls))])
                    (add-to-class-env! c-name
                                       (a-class s-name f-env
                                                (merge-method-envs
                                                 (class->method-env (lookup-class s-name))
                                                 (method-decls->method-env
                                                  m-decls c-name (field-env->field-names f-env))))))]))

(define (field-decls->field-env c-name f-decls)
  (if (null? f-decls)
      '()
      (cases field-decl (car f-decls)
        [a-field-decl (acc name)
                      (cons (cons name (a-field acc c-name))
                            (field-decls->field-env c-name (cdr f-decls)))])))

(define (field-env->field-names fe)
  (if (null? fe)
      '()
      (cons (caar fe)
            (field-env->field-names (cdr fe)))))

(define (append-field-env s-fielde new-fielde)
  (if (null? s-fielde)
      new-fielde
      (let ([s-field (car s-fielde)])
        (cases field (cdr s-field)
          [a-field (acc c-name)
                   (cons (if (or
                              (assv (car s-field) new-fielde)
                              (private-acc? acc))
                             (cons (new-identifier (car s-field))
                                   (cdr s-field))
                             s-field)
                         (append-field-env (cdr s-fielde)
                                        new-fielde))]))))

(define new-identifier
  (let ([i 0])
    (lambda (p)
      (set! i (+ i 1))
      (string->symbol
       (string-append
        (symbol->string p)
        (number->string i))))))

(define-datatype field field?
  (a-field
   (acc accessibility?)
   (c-name identifier?)))

(define-datatype class class?
  [a-class
   (super-name (maybe identifier?))
   (field-env (list-of pair?))
   (method-env method-environment?)])

(define (class->field-env c)
  (cases class c
    [a-class (s-name fe m-env)
             fe]))

(define (class->super-name c)
  (cases class c
    [a-class (s-name fe m-env)
             s-name]))

(define (class->method-env c)
  (cases class c
    [a-class (s-name fe m-env)
             m-env]))

(define (find-field c-name f-name)
  (let ([p (assv f-name (class->field-env (lookup-class c-name)))])
    (if p
        (cdr p)
        (eopl:error 'find-field
                    "field ~A not found in class ~A"
                    f-name c-name))))

(define (find-method c-name name)
  (let ([p (assv name (class->method-env (lookup-class c-name)))])
    (if p
        (cdr p)
        (eopl:error 'find-method
                    "method ~A not found in class ~A"
                    name c-name))))

(define (method-decls->method-env m-decls c-name f-names)
  (map (lambda (m-decl)
         (cases method-decl m-decl
           [a-method-decl (acc m-name vars body)
                          (cons m-name
                                (a-method vars body c-name f-names acc))]))
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
   (c-name identifier?)
   (field-names (list-of identifier?))
   (acc accessibility?)])

(define (method->class-name m)
  (cases method m
    [a-method (vars body c-name f-names acc)
              c-name]))

(define (public-acc? acc)
  (cases accessibility acc
    [public-acc () #t]
    [else #f]))

(define (protected-acc? acc)
  (cases accessibility acc
    [protected-acc () #t]
    [else #f]))

(define (private-acc? acc)
  (cases accessibility acc
    [private-acc () #t]
    [else #f]))

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
               (unless (= (length vars)
                          (length refs))
                 (eopl:error 'apply-procedure
                             "argument number mismatch, expecting ~A, got ~A"
                             (length vars)
                             (length refs)))
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
  (pair-val
   (pair pair?))
  (null-val))

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
    [pair-val (proc) proc]
    [else
     (eopl:error 'expval->proc "expval ~A is not pair" val)]))

(define (expval-null? val)
  (cases expval val
    [null-val () #t]
    [else #f]))

(define (expval-pair? val)
  (cases expval val
    [pair-val (v) #t]
    [else #f]))

;;;;;;;;;;;;; interpreter  ;;;;;;;;;;;;;;;

(define (run prog)
  (cases program (scan&parse prog)
    [a-program (class-decls exp)
               (init-store)
               (init-class-env! class-decls)
               (value-of exp (empty-env))]))

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
    [letrec-exp (p-names b-varss bodies exp)
                (value-of exp (extend-env-rec p-names b-varss bodies env))]

    ;;; procedures
    [proc-exp (vars exp)
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
               (let rec ([val (value-of exp1 env)]
                         [need-par #t])
                 (cases expval val
                   [num-val (num)
                            (display num)]
                   [bool-val (bool)
                             (display bool)]
                   [proc-val (proc)
                             (display "#procedure")]
                   [null-val ()
                             (display "()")]
                   [pair-val (p)
                             (when need-par
                               (display "("))
                             (rec (car p) #t)
                             (cond
                               [(expval-null? (cdr p))
                                (display ")")]
                               [(expval-pair? (cdr p))
                                (display " ")
                                (rec (cdr p) #f)]
                               [else
                                (display " . ")
                                (rec (cdr p) #f)
                                (display ")")])]
                   ))
               (newline)
               (num-val 1)]
    [null-exp ()
              (null-val)]
    [null?-exp (exp1)
               (bool-val (expval-null? (value-of exp1 env)))]
    [car-exp (exp1)
             (car (expval->pair (value-of exp1 env)))]
    [cdr-exp (exp1)
             (cdr (expval->pair (value-of exp1 env)))]
    [cons-exp (exp1 exp2)
              (pair-val (cons (value-of exp1 env)
                              (value-of exp2 env)))]
    [list-exp (exps)
              (make-list (values-of-exps exps env))]

    [self-exp ()
              (apply-env env '%self)]
    [method-call-exp (obj-exp m-name rands)
                     (let ([obj (value-of obj-exp env)])
                       (apply-method
                        (object->class-name obj)
                        m-name
                        obj
                        (values-of-exps rands env)
                        env))]
    [super-call-exp (m-name rands)
                    (apply-method (apply-env env '%super)
                                  m-name
                                  (apply-env env '%self)
                                  (values-of-exps rands env)
                                  env)]
    [new-object-exp (c-name rands)
                    (let ([obj (new-object c-name)])
                      (apply-method c-name 'initialize
                                    obj
                                    (values-of-exps rands env)
                                    env)
                      obj)]
    [fieldref-exp (exp1 f-name)
                  (let ([obj (value-of exp1 env)])
                    (deref (field-ref obj f-name env)))]
    [fieldset-exp (exp1 f-name exp2)
                  (let ([obj (value-of exp1 env)])
                    (setref! (field-ref obj f-name env)
                             (value-of exp2 env)))]
    ))

(define (field-ref obj f-name env)
  (cases object obj
    [an-object (c-name fs)
               (cases field (find-field c-name f-name)
                 [a-field (acc class-name)
                          (let ([self0 (current-self env)])
                            (unless (or
                                     (and
                                      (private-acc? acc)
                                      self0
                                      (eqv? class-name (object->class-name self0)))
                                     (and
                                      (protected-acc? acc)
                                      self0
                                      (instance-of? self0 c-name))
                                     (public-acc? acc))
                              (eopl:error 'field-ref
                                          "field ~A in class ~A is unaccessible"
                                          f-name class-name)))
                          (list-ref fs
                                    (location f-name (class->field-env (lookup-class c-name))
                                              (lambda (f-name field)
                                                (eqv? f-name (car field)))))])]))

(define (apply-method c-name m-name self args env)
  (cases method (find-method c-name m-name)
    [a-method (vars body class-name field-names acc)
              (let ([self0 (current-self env)])
                (unless (or
                         (and
                          (private-acc? acc)
                          self0
                          (eqv? class-name (object->class-name self0)))
                         (and
                          (protected-acc? acc)
                          self0
                          (instance-of? self0 c-name))
                         (public-acc? acc))
                  (eopl:error 'apply-method
                              "method ~A in class ~A is unaccessible"
                              m-name class-name)))
              (value-of body
                        (extend-env* vars
                                     (map newref args)
                                     (extend-env-with-self-and-super
                                      self
                                      (class->super-name (lookup-class class-name))
                                      (extend-env* field-names
                                                   (object->fields self)
                                                   (empty-env)))))]))

(define (instance-of? obj c-name)
  (let loop ([cn (object->class-name obj)])
    (if (eqv? cn c-name)
        #t
        (let ([s-name (class->super-name (lookup-class cn))])
          (if s-name
              (loop s-name)
              #f)))))

(define (make-list vals)
  (if (null? vals)
      (null-val)
      (pair-val (cons (car vals)
                      (make-list (cdr vals))))))

(define (values-of-exps exps env)
  (if (null? exps)
      '()
      (cons (value-of (car exps) env)
            (values-of-exps (cdr exps) env))))

(define (new-object c-name)
  (an-object c-name
             (map (lambda (f)
                    (newref (list 'uninitialized (car f))))
                  (class->field-env (lookup-class c-name)))))

;;;;;;;;;;;; ;;;;;;;;;;;;;  test ;;;;;;;;;;;;;;;;;;;;

(define (test val prg)
  (let ([val1 (run prg)])
    (unless (equal? val val1)
      (eopl:error 'test
                  "test failed, ~A != ~A"
                  val val1))))

(test (make-list
       (list
        (make-list
         (list (num-val 3)
               (num-val -3)))
        (make-list
         (list (num-val 5)
               (num-val -5)))))
      "
class c1 extends object
 field private i
 field private j
 method public initialize (x)
 begin
  set i = x;
  set j = -(0,x);
 end
 method public countup(d)
 begin
  set i = +(i,d);
  set j = -(j,d);
 end
 method public get() list(i,j)

let t1 = 0
 t2 = 0
 o1 = new c1(3)
in begin
 set t1 = send o1 get();
 send o1 countup(2);
 set t2 = send o1 get();
 list(t1, t2);
end
")

(test (num-val 12)
      "
class node extends object
 field private left
 field private right
 method public initialize (l, r)
  begin
   set left = l;
   set right = r;
  end
 method public sum() +(send left sum(), send right sum())
class leaf extends object
 field private value
 method public initialize(x) set value = x
 method public sum() value
send new node(
      new node(
       new leaf(3),
       new leaf(4)),
      new leaf(5)) sum()
")

(test (make-list
       (list
        (num-val 1)
        (num-val 0)
        (num-val 0)
        (num-val 1)))
      "
class oe extends object
 method public initialize()
  1
 method public even(n)
  if zero?(n) then 1 else send self odd(-(n,1))
 method public odd(n)
  if zero?(n) then 0 else send self even(-(n,1))
let o1 = new oe()
in list(send o1 odd(13),
        send o1 odd(14),
        send o1 even(15),
        send o1 even(16))
")

(test (make-list
       (list
        (num-val 101)
        (num-val 102)
        (num-val 101)
        (num-val 999)))
      "
class c1 extends object
 field protected x
 field protected y
 method public initialize() 1
 method public setx1(v) set x = v
 method public sety1(v) set y = v
 method public getx1() x
 method public gety1() y
class c2 extends c1
 field protected y
 method public sety2(v) set y = v
 method public getx2() x
 method public gety2() y
let o2 = new c2()
in begin
 send o2 setx1(101);
 send o2 sety1(102);
 send o2 sety2(999);
 list(send o2 getx1(),
      send o2 gety1(),
      send o2 getx2(),
      send o2 gety2());
end
")

(test (make-list
       (list
        (num-val 11)
        (num-val 22)
        (num-val 22)))
      "
class c1 extends object
 method public initialize() 1
 method public m1() 11
 method public m2() send self m1()
class c2 extends c1
 method public m1() 22
list(send new c1() m1(),
     send new c2() m1(),
     send new c2() m2())
")

(test (make-list
       (list
        (num-val 23)
        (num-val 33)))
      "
class c1 extends object
 method public initialize() 1
 method public m1() send self m2()
 method public m2() 13
class c2 extends c1
 method public m1() 22
 method public m2() 23
 method public m3() super m1()
class c3 extends c2
 method public m1() 32
 method public m2() 33
list(send new c2() m3(),
     send new c3() m3())
")

(test (num-val 22)
      "
class c1 extends object
 method protected initialize() 1
 method protected m1()
  begin
   send self m4();
   send self m2();
  end
 method protected m2() 12
 method private m3() 13
class c2 extends c1
 method public initialize()
  begin
   super initialize();
   send self m1();
   send self m4();
  end
 method public m1() super m1()
 method private m2() 22
 method private m4() 21
let o = new c2()
in
begin
 send o m1();
end")

(test (make-list
       (list
        (make-list
         (list
          (num-val 333)
          (num-val 20)))
        (make-list
         (list
          (num-val 10)
          (num-val 200)))
        (make-list
         (list
          (num-val 1)
          (num-val 20)
          (num-val 3)))
        (make-list
         (list
          (num-val 11)
          (num-val 22)
          (num-val 333)))
        (make-list
         (list
          (num-val 10)
          (num-val 200)
          (num-val 3)))))
      "
class c1 extends object
 field public x
 field protected y
 field private z
 method public initialize()
  begin
   set x = 1;
   set y = 2;
   set z = 3;
  end
 method public get1() list(x, y, z)
class c2 extends c1
 field public u
 field protected v
 field private x
 method public initialize()
  begin
   super initialize();
   set u = 11;
   set v = 22;
   set x = 33;
  end
 method public get2() list(u, v, x)
 method public m1()
  begin
   fieldset self x = 333;
   fieldset self y = 20;
   list(fieldref self x,
        fieldref self y);
  end
 method public m2(o1)
  begin
   fieldset o1 x = 10;
   fieldset o1 y = 200;
   list(fieldref o1 x,
        fieldref o1 y);
  end
let o2 = new c2()
    o1 = new c1()
in
 list(send o2 m1(),
      send o2 m2(o1),
      send o2 get1(),
      send o2 get2(),
      send o1 get1())
")

(provide run)