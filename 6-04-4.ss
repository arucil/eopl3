#lang eopl

(define-datatype continuation continuation?
  [end-cont]
  [remove-first-cont
   (ls list?)
   (k continuation?)]
  [list-sum-cont
   (ls list?)
   (k continuation?)]
  [occurs-free1-cont
   (x symbol?)
   (exp list?)
   (k continuation?)]
  [occurs-free2-cont
   (val1 boolean?)
   (k continuation?)]
  [subst1-cont
   (new symbol?)
   (old symbol?)
   (ls list?)
   (k continuation?)]
  [subst2-cont
   (val1 (lambda (v) #t))
   (k continuation?)]
  )

(define cont 'ha)
(define val 'ha)
(define new-val 'ha)
(define list1 'ha)
(define exp 'ha)

(define (apply-cont)
  (cases continuation cont
    [end-cont ()
     (eopl:printf "end of computation.~%")
     val]
    [remove-first-cont (ls k)
                       (set! cont k)
                       (set! val (cons (car ls) val))
                       (apply-cont)]
    [list-sum-cont (ls k)
                   (set! cont k)
                   (set! val (+ (car ls) val))
                   (apply-cont)]
    [occurs-free1-cont (x exp1 k)
                       (set! cont (occurs-free2-cont val k))
                       (set! exp (cadr exp1))
                       (set! val x)
                       (occurs-free?/k)]
    [occurs-free2-cont (val1 k)
                       (set! cont k)
                       (set! val (or val1 val))
                       (apply-cont)]
    [subst1-cont (new old ls k)
                 (set! cont (subst2-cont val k))
                 (set! val old)
                 (set! new-val new)
                 (set! list1 (cdr ls))
                 (subst/k)]
    [subst2-cont (val1 k)
                 (set! cont k)
                 (set! val (cons val1 val))
                 (apply-cont)]
    ))

;; remove-first
(define (remove-first x ls)
  (set! cont (end-cont))
  (set! val x)
  (set! list1 ls)
  (remove-first/k))

(define (remove-first/k)
  (cond
    [(null? list1)
     (set! val '())
     (apply-cont)]
    [(eqv? val (car list1))
     (set! val (cdr list1))
     (apply-cont)]
    [else
     (set! cont (remove-first-cont list1 cont))
     (set! list1 (cdr list1))
     (remove-first/k)]))

;; list-sum
(define (list-sum ls)
  (set! cont (end-cont))
  (set! list1 ls)
  (list-sum/k))

(define (list-sum/k)
  (if (null? list1)
      (begin
        (set! val 0)
        (apply-cont))
      (begin
        (set! cont (list-sum-cont list1 cont))
        (set! list1 (cdr list1))
        (list-sum/k))))

;;; occurs-free?
(define (occurs-free? x exp1)
  (set! val x)
  (set! exp exp1)
  (set! cont (end-cont))
  (occurs-free?/k))

(define (occurs-free?/k)
  (cond
    [(symbol? exp)
     (set! val (eqv? val exp))
     (apply-cont)]
    [(eqv? (car exp) 'lambda)
     (if (eqv? val (caadr exp))
         (begin
           (set! val #f)
           (apply-cont))
         (begin
           (set! exp (caddr exp))
           (occurs-free?/k)))]
    [else
     (set! cont (occurs-free1-cont val exp cont))
     (set! exp (car exp))
     (occurs-free?/k)]))

;;; subst
(define (subst new old ls)
  (set! val old)
  (set! new-val new)
  (set! list1 ls)
  (set! cont (end-cont))
  (subst/k))

(define (subst/k)
  (if (null? list1)
      (begin
        (set! val '())
        (apply-cont))
      (begin
        (set! cont (subst1-cont new-val val list1 cont))
        (set! list1 (car list1))
        (subst-sexp/k))))

(define (subst-sexp/k)
  (if (symbol? list1)
      (begin
        (set! val (if (eqv? val list1)
                      new-val
                      list1))
        (apply-cont))
      (subst/k)))