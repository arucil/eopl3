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
   (body expression?)
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-vars (list-of (list-of identifier?)))
   (bodies (list-of expression?))
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
   (body expression?)
   (env environment?)))

(define (apply-procedure p vals)
  (cases proc p
    [procedure (vars body env)
               (value-of body
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
  (cases program (anf-of-program (scan&parse prog))
    [a-program (exp)
      (value-of exp (empty-env))]))

(define (value-of exp env)
  (cases expression exp
    [const-exp (num)
      (num-val num)]
    [diff-exp (exp1 exp2)
              (num-val (-
                        (expval->num (value-of exp1 env))
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
    [letrec-exp (p-names b-varss p-bodies body)
                (value-of body (extend-env-rec* p-names b-varss p-bodies env))]

    ;;; procedures
    [proc-exp (vars body)
              (proc-val (procedure vars body env))]

    [call-exp (exp1 exps)
              (apply-procedure (expval->proc (value-of exp1 env))
                               (map (lambda (x)
                                      (value-of x env))
                                    exps))]))

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
      (let ([id (string->symbol
                 (string-append (symbol->string prefix)
                                (number->string counter)))])
        (set! counter (+ counter 1))
        id))))

;;;;;;;;;;;;;;  translator  ;;;;;;;;;;;;;;

(define (anf-of-program prog)
  (cases program prog
    [a-program (exp1)
               (a-program
                (anf-of-exp exp1))]))

(define (anf-of-exps exps builder)
  (let anf-of-rest ([exps exps] [acc '()])
    (cond
      [(null? exps)
       (builder (reverse acc))]
      [(inp-exp-simple? (car exps))
       (anf-of-rest (cdr exps)
                    (cons (car exps)
                          acc))]
      [else
       (let ([var (new-identifier 'var)])
         (let-exp var
                  (anf-of-exp (car exps))
                  (anf-of-rest (cdr exps)
                               (cons (var-exp var) acc))))])))

(define (inp-exp-simple? exp)
  (cases expression exp
    [const-exp (n) #t]
    [var-exp (v) #t]
    [proc-exp (ids exp) #t]
    [else #f]))

(define (anf-of-exp exp)
  (cases expression exp
    [zero?-exp (exp1)
               (anf-of-exps (list exp1)
                            (lambda (simples)
                              (zero?-exp (car simples))))]
    [diff-exp (exp1 exp2)
              (anf-of-exps (list exp1 exp2)
                           (lambda (simples)
                             (diff-exp (car simples)
                                       (cadr simples))))]
    [if-exp (exp1 exp2 exp3)
            (anf-of-exps (list exp1)
                         (lambda (simples)
                           (if-exp (car simples)
                                   (anf-of-exp exp2)
                                   (anf-of-exp exp3))))]
    [let-exp (var exp1 body)
             (anf-of-exps (list exp1)
                          (lambda (simples)
                            (let-exp var (car simples)
                                         (anf-of-exp body))))]
    [letrec-exp (p-names b-varss p-bodies body)
                (letrec-exp p-names
                            b-varss
                            (map (lambda (p-body) (anf-of-exp p-body))
                                 p-bodies)
                            (anf-of-exp body))]
    [call-exp (rator rands)
              (anf-of-exps (cons rator rands)
                           (lambda (simples)
                             (call-exp (car simples)
                                           (cdr simples))))]
    [else exp]
    ))

;;;;;;;;;;;;;  print  ;;;;;;;;;;;;;

(define (indent i)
  (string-append i " "))

(define (print-program prog)
  (cases program (anf-of-program (scan&parse prog))
    [a-program (exp1)
                   (letrec ([disp (lambda (exp ind)
                                    (cases expression exp
                                      [if-exp (simple1 exp2 exp3)
                                              (eopl:printf "~Aif " ind)
                                              (disp simple1 (indent ind))
                                              (eopl:printf "~%~Athen~%" ind)
                                              (disp exp2 (indent ind))
                                              (eopl:printf "~%~Aelse~%" ind)
                                              (disp exp3 (indent ind))]
                                      [let-exp (var simple1 body)
                                               (eopl:printf "~Alet ~s = " ind var)
                                               (disp simple1 (indent ind))
                                               (eopl:printf "~%~Ain~%" ind)
                                               (disp body (indent ind))]
                                      [letrec-exp (p-names b-varss p-bodies body)
                                                  (eopl:printf "~Aletrec~%" ind)
                                                  (set! ind (indent ind))
                                                  (let rec ([p-names p-names]
                                                            [b-varss b-varss]
                                                            [p-bodies p-bodies])
                                                    (when (not (null? p-names))
                                                      (eopl:printf "~A~s~A = ~%" ind (car p-names)
                                                                   (car b-varss))
                                                      (disp(car p-bodies) (indent ind))
                                                      (newline)
                                                      (rec (cdr p-names)
                                                        (cdr b-varss)
                                                        (cdr p-bodies))))
                                                  (eopl:printf "in~%")
                                                  (disp body ind)]
                                      [call-exp (rator rands)
                                                (eopl:printf "~A(" ind)
                                                (disp rator (indent ind))
                                                (for-each (lambda (simple1)
                                                            (display " ")
                                                            (disp simple1 (indent ind)))
                                                          rands)
                                                (display ")")]
                                      [const-exp (n)
                                                 (display n)]
                                      [var-exp (v)
                                               (display v)]
                                      [zero?-exp (exp1)
                                                 (display "zero?(")
                                                 (disp exp1 (indent ind))
                                                 (display ")")]
                                      [diff-exp (exp1 exp2)
                                                (display "-(")
                                                (disp exp1 (indent ind))
                                                (display ", ")
                                                (disp exp2 (indent ind))
                                                (display ")")]
                                      [proc-exp (vars body)
                                                (eopl:printf "proc ~A ~%" vars)
                                                (disp body (indent ind))]))])
                     (disp exp1 "")
                     (newline))]))