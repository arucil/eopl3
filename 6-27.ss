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

(define the-cps-grammar
  '((cps-program (cps-tf-exp) cps-a-program)

    ;;; simple
    (cps-simple-exp
     (number)
     cps-const-exp)

    (cps-simple-exp
     (identifier)
     cps-var-exp)

    (cps-simple-exp
     ("-" "(" cps-simple-exp "," cps-simple-exp ")")
     cps-diff-exp)

    (cps-simple-exp
     ("zero?" "(" cps-simple-exp ")")
     cps-zero?-exp)

    (cps-simple-exp
     ("proc" "(" (separated-list identifier ",") ")" cps-tf-exp)
     cps-proc-exp)

    ;; tail form
    (cps-tf-exp
     (cps-simple-exp)
     simple-exp->exp)

    (cps-tf-exp
     ("let" identifier "=" cps-simple-exp "in" cps-tf-exp)
     cps-let-exp)

    (cps-tf-exp
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" cps-tf-exp) "in" cps-tf-exp)
     cps-letrec-exp)

    (cps-tf-exp
     ("if" cps-simple-exp "then" cps-tf-exp "else" cps-tf-exp)
     cps-if-exp)

    (cps-tf-exp
     ("(" cps-simple-exp (arbno cps-simple-exp) ")")
     cps-call-exp)
    
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
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression)
     letrec-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-cps-grammar)
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;  environment ;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name identifier?)
   (b-vars (list-of identifier?))
   (body cps-tf-exp?)
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-vars (list-of (list-of identifier?)))
   (bodies (list-of cps-tf-exp?))
   (env environment?)))

(define (extend-env* vars vals env)
  (let loop ([vars vars]
             [vals vals]
             [e env])
    (if (null? vars)
        e
        (loop (cdr vars)
              (cdr vals)
              (extend-env (car vars)
                          (car vals)
                          e)))))

(define (apply-env env svar)
  (cases environment env
    [empty-env ()
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [extend-env (var val env)
                (if (eqv? var svar)
                    val
                    (apply-env env svar))]
    [extend-env-rec (pname bvar body e)
                    (if (eqv? svar pname)
                        (proc-val (procedure bvar body env))
                        (apply-env e svar))]
    [extend-env-rec* (pnames bvars bodies e)
                     (let loop ([pnames pnames]
                                [bvars bvars]
                                [bodies bodies])
                       (cond
                         [(null? pnames)
                          (apply-env e svar)]
                         [(eqv? (car pnames) svar)
                          (proc-val (procedure (car bvars) (car bodies) env))]
                         [else
                          (loop (cdr pnames)
                                (cdr bvars)
                                (cdr bodies))]))]
    ))

;;;;;;;;;;;;;;  procedure  ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body cps-tf-exp?)
   (env environment?)))

(define (apply-procedure/k p vals)
  (cases proc p
    [procedure (vars body env)
               (value-of/k body
                           (extend-env* vars vals env))]))

;;;;;;;;;;;;;; expval    ;;;;;;;;;;;;;
                
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

;;;;;;;;;;;;;;;;  interpreter  ;;;;;;;;;;;;;;;;

(define (run prog)
  (cases cps-program (cps-of-program (scan&parse prog))
    [cps-a-program (exp)
      (value-of/k exp (empty-env))]))

(define (run-org prog)
  (cases cps-program ((sllgen:make-string-parser the-lexical-spec the-cps-grammar) prog)
    [cps-a-program (exp)
      (value-of/k exp (empty-env))]))

(define (value-of/k exp env)
  (cases cps-tf-exp exp
    [simple-exp->exp (simple)
                     (value-of-simple-exp simple env)]
    [cps-let-exp (var exp1 body)
                 (value-of/k body
                             (extend-env var
                                         (value-of-simple-exp exp1 env)
                                         env))]
    [cps-letrec-exp (p-names b-varss p-bodies body)
                    (value-of/k body
                                (extend-env-rec* p-names b-varss p-bodies env))]
    [cps-if-exp (simple1 exp1 exp2)
                (if (expval->bool (value-of-simple-exp simple1 env))
                    (value-of/k exp1 env)
                    (value-of/k exp2 env))]
    [cps-call-exp (rator rands)
                  (apply-procedure/k (expval->proc
                                      (value-of-simple-exp rator env))
                                     (map (lambda (x)
                                            (value-of-simple-exp x env))
                                          rands))]
    ))

(define (value-of-simple-exp exp env)
  (cases cps-simple-exp exp
    [cps-const-exp (num)
                   (num-val num)]
    [cps-var-exp (var)
                 (apply-env env var)]
    [cps-diff-exp (simple1 simple2)
                  (num-val (- (expval->num (value-of-simple-exp simple1 env))
                              (expval->num (value-of-simple-exp simple2 env))))]
    [cps-zero?-exp (simple1)
                   (bool-val (zero? (expval->num (value-of-simple-exp simple1 env))))]
    [cps-proc-exp (vars body)
                  (proc-val (procedure vars body env))]
    ))

;;;;;;;;;;;;;;;  aux  ;;;;;;;;;;;;;;;;;;;

(define (list-index pred ls)
  (let loop ([ls ls]
             [n 0])
    (cond
      [(null? ls) #f]
      [(pred (car ls)) n]
      [else
       (loop (cdr ls) (+ n 1))])))

(define (list-set ls i x)
  (cond
    [(null? ls) '()]
    [(zero? i)
     (cons x (cdr ls))]
    [else
     (cons (car ls)
           (list-set (cdr ls)
                     (- i 1)
                     x))]))

(define new-identifier
  (let ([counter 0])
    (lambda (prefix)
      (set! counter (+ counter 1))
      (string->symbol
       (string-append
        (symbol->string prefix)
        (number->string counter))))))

;;;;;;;;;;;;;;  translator  ;;;;;;;;;;;;;;

(define (cps-of-program prog)
  (cases program prog
    [a-program (exp1)
               (cps-a-program
                (cps-of-exps (list exp1)
                             (lambda (v)
                               (simple-exp->exp (car v)))))]))

(define (cps-of-exps exps builder)
  (let cps-of-rest ([exps exps])
    (let ([pos (list-index
                (lambda (exp)
                  (not (inp-exp-simple? exp)))
                exps)])
      (if pos
          (let ([var (new-identifier 'var)])
            (cps-of-exp (list-ref exps pos)
                        (cps-proc-exp (list var)
                                      (cps-of-rest (list-set exps pos (var-exp var))))))
          (builder (map cps-of-simple-exp exps))))))

(define (inp-exp-simple? exp)
  (cases expression exp
    [const-exp (n) #t]
    [var-exp (v) #t]
    [diff-exp (exp1 exp2)
              (and (inp-exp-simple? exp1)
                   (inp-exp-simple? exp2))]
    [zero?-exp (exp1)
               (inp-exp-simple? exp1)]
    [proc-exp (ids exp) #t]
    [else #f]))

(define (make-send-to-cont k-exp simple1)
  (cases cps-simple-exp k-exp
    [cps-proc-exp (vars body)
                  (subst-free body (car vars) simple1)]
    [else
     (cps-call-exp k-exp (list simple1))]))

(define (subst-free old-simple var new-simple)
  (letrec ([subst-simple
            (lambda (old-simple)
              (cases cps-simple-exp old-simple
                [cps-var-exp (var1)
                             (if (eqv? var var1)
                                 new-simple
                                 old-simple)]
                [cps-diff-exp (simple1 simple2)
                              (cps-diff-exp (subst-simple simple1)
                                            (subst-simple simple2))]
                [cps-zero?-exp (simple1)
                               (cps-zero?-exp (subst-simple simple1))]
                [cps-proc-exp (ids exp)
                              (if (list-index (lambda (x) (eqv? x var))
                                              ids)
                                  old-simple
                                  (cps-proc-exp ids
                                                (subst-tf exp)))]
                [else old-simple]))]
           [subst-tf
            (lambda (old-exp)
              (cases cps-tf-exp old-exp
                [simple-exp->exp (simple1)
                                 (simple-exp->exp
                                  (subst-simple simple1))]
                [cps-if-exp (simple1 exp2 exp3)
                            (cps-if-exp (subst-simple simple1)
                                        (subst-tf exp2)
                                        (subst-tf exp3))]
                [cps-let-exp (var1 simple1 body)
                             (cps-let-exp var1
                                          (subst-simple simple1)
                                          (if (eqv? var1 var)
                                              body
                                              (subst-tf body)))]
                [cps-letrec-exp (p-names b-varss p-bodies body)
                                (letrec ([subst-bodies
                                          (lambda (b-varss p-bodies)
                                            (if (null? b-varss)
                                                '()
                                                (cons (if (list-index (lambda (x)
                                                                        (eqv? x var))
                                                                      (car b-varss))
                                                          (car p-bodies)
                                                          (subst-tf (car p-bodies)))
                                                      (subst-bodies (cdr b-varss)
                                                                    (cdr p-bodies)))))])
                                  (cps-letrec-exp p-names
                                                  b-varss
                                                  (subst-bodies b-varss p-bodies)
                                                  (if (list-index (lambda (x)
                                                                    (eqv? x var))
                                                                  p-names)
                                                      body
                                                      (subst-tf body))))]
                [cps-call-exp (rator rands)
                              (cps-call-exp (subst-simple rator)
                                            (map subst-simple rands))]))])
    (subst-tf old-simple)))
       
(define (cps-of-exp exp k-exp)
  (cases expression exp
    [zero?-exp (exp1)
               (cps-of-exps (list exp1)
                            (lambda (simples)
                              (make-send-to-cont k-exp
                                                 (cps-zero?-exp (car simples)))))]
    [diff-exp (exp1 exp2)
              (cps-of-exps (list exp1 exp2)
                           (lambda (simples)
                             (make-send-to-cont k-exp
                                                (cps-diff-exp (car simples)
                                                              (cadr simples)))))]
    [if-exp (exp1 exp2 exp3)
            (cps-of-exps (list exp1)
                         (lambda (simples)
                           (cases cps-simple-exp k-exp
                             [cps-var-exp (v)
                              (cps-if-exp (car simples)
                                          (cps-of-exp exp2 k-exp)
                                          (cps-of-exp exp3 k-exp))]
                             [else
                              (let ([k-var (new-identifier 'k%)])
                                (cps-let-exp k-var
                                             k-exp
                                             (cps-if-exp (car simples)
                                                         (cps-of-exp exp2 (cps-var-exp k-var))
                                                         (cps-of-exp exp3 (cps-var-exp k-var)))))])))]
    [let-exp (var exp1 body)
             (cps-of-exp exp1
                         (cps-proc-exp (list var)
                                       (cps-of-exp body k-exp)))]
    [letrec-exp (p-names b-varss p-bodies body)
                (cps-letrec-exp p-names
                                (map (lambda (b-vars) (append b-vars (list 'k%00)))
                                     b-varss)
                                (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00)))
                                     p-bodies)
                                (cps-of-exp body k-exp))]
    [call-exp (rator rands)
              (cps-of-exps (cons rator rands)
                           (lambda (simples)
                             (cps-call-exp (car simples)
                                           (append (cdr simples) (list k-exp)))))]
    [else
     (make-send-to-cont k-exp
                        (cps-of-simple-exp exp))]
    ))

(define (cps-of-simple-exp exp)
  (cases expression exp
    [const-exp (n)
               (cps-const-exp n)]
    [var-exp (v)
             (cps-var-exp v)]
    [diff-exp (exp1 exp2)
              (cps-diff-exp
               (cps-of-simple-exp exp1)
               (cps-of-simple-exp exp2))]
    [zero?-exp (exp1)
               (cps-zero?-exp (cps-of-simple-exp exp1))]
    [proc-exp (vars body)
              (cps-proc-exp (append vars (list 'k%00))
                            (cps-of-exp body (cps-var-exp 'k%00)))]
    [else 'error]))

;;;;;;;;;;;;;  print  ;;;;;;;;;;;;;

(define (indent i)
  (string-append i " "))

(define (print-program prog)
  (cases cps-program (cps-of-program (scan&parse prog))
    [cps-a-program (exp1)
                   (letrec ([tf (lambda (exp ind)
                                (cases cps-tf-exp exp
                                  [simple-exp->exp (simple1)
                                                   (display ind)
                                                   (simple simple1 (indent ind))]
                                  [cps-if-exp (simple1 exp2 exp3)
                                          (eopl:printf "~Aif " ind)
                                          (simple simple1 (indent ind))
                                          (eopl:printf "~%~Athen~%" ind)
                                          (tf exp2 (indent ind))
                                          (eopl:printf "~%~Aelse~%" ind)
                                          (tf exp3 (indent ind))]
                                  [cps-let-exp (vars simples body)
                                               (eopl:printf "~Alet~%" ind)
                                               (let loop ([vars vars]
                                                          [simples simples])
                                                 (unless (null? vars)
                                                   (eopl:printf "~A~s = " (indent ind) (car vars))
                                                   (simple (car simples) (indent (indent ind)))
                                                   (newline)
                                                   (loop (cdr vars) (cdr simples))))
                                               (eopl:printf "~Ain~%" ind)
                                               (tf body (indent ind))]
                                  [cps-letrec-exp (p-names b-varss p-bodies body)
                                                  (eopl:printf "~Aletrec~%" ind)
                                                  (set! ind (indent ind))
                                                  (let rec ([p-names p-names]
                                                            [b-varss b-varss]
                                                            [p-bodies p-bodies])
                                                    (unless (null? p-names)
                                                      (eopl:printf "~A~s~A = ~%" ind (car p-names)
                                                                   (car b-varss))
                                                      (tf (car p-bodies) (indent ind))
                                                      (newline)
                                                      (rec (cdr p-names)
                                                        (cdr b-varss)
                                                        (cdr p-bodies))))
                                                  (eopl:printf "in~%")
                                                  (tf body ind)]
                                  [cps-call-exp (rator rands)
                                                (eopl:printf "~A(" ind)
                                                (simple rator (indent ind))
                                                (for-each (lambda (simple1)
                                                            (display " ")
                                                            (simple simple1 (indent ind)))
                                                          rands)
                                                (display ")")]
                                  ))]
                            [simple (lambda (simple1 ind)
                                      (cases cps-simple-exp simple1
                                        [cps-const-exp (n)
                                                       (display n)]
                                        [cps-var-exp (v)
                                                     (display v)]
                                        [cps-zero?-exp (exp1)
                                                       (display "zero?(")
                                                       (simple exp1 (indent ind))
                                                       (display ")")]
                                        [cps-diff-exp (exp1 exp2)
                                                      (display "-(")
                                                      (simple exp1 (indent ind))
                                                      (display ", ")
                                                      (simple exp2 (indent ind))
                                                      (display ")")]
                                        [cps-proc-exp (vars body)
                                                      (eopl:printf "proc ~A ~%" vars)
                                                      (tf body (indent ind))]
                                        ))])
                     (tf exp1 "")
                     (newline))]))