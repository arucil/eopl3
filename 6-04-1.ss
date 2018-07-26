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

(define (apply-cont k v)
  (cases continuation k
    [end-cont ()
     (eopl:printf "end of computation.~%")
     v]
    [remove-first-cont (ls k)
                       (apply-cont k (cons (car ls) v))]
    [list-sum-cont (ls k)
                   (apply-cont k (+ (car ls) v))]
    [occurs-free1-cont (x exp k)
                       (occurs-free?/k x (cadr exp)
                                       (occurs-free2-cont v k))]
    [occurs-free2-cont (val1 k)
                       (apply-cont k (or val1 v))]
    [subst1-cont (new old ls k)
                 (subst/k new old (cdr ls)
                          (subst2-cont v k))]
    [subst2-cont (val1 k)
                 (apply-cont k (cons val1 v))]
    ))

(define (remove-first x ls)
  (remove-first/k x ls (end-cont)))

(define (remove-first/k x ls k)
  (cond
    [(null? ls)
     (apply-cont k '())]
    [(eqv? x (car ls))
     (apply-cont k (cdr ls))]
    [else
     (remove-first/k x (cdr ls)
                     (remove-first-cont ls k))]))

(define (list-sum ls)
  (list-sum/k ls (end-cont)))

(define (list-sum/k ls k)
  (if (null? ls)
      (apply-cont k 0)
      (list-sum/k (cdr ls)
                (list-sum-cont ls k))))

(define (occurs-free? x exp)
  (occurs-free?/k x exp (end-cont)))

(define (occurs-free?/k x exp k)
  (cond
    [(symbol? exp)
     (apply-cont k (eqv? x exp))]
    [(eqv? (car exp) 'lambda)
     (if (eqv? x (caadr exp))
         (apply-cont k #f)
         (occurs-free?/k x (caddr exp) k))]
    [else
     (occurs-free?/k x (car exp)
                     (occurs-free1-cont x exp k))]))

(define (subst new old ls)
  (subst/k new old ls (end-cont)))

(define (subst/k new old ls k)
  (if (null? ls)
      (apply-cont k '())
      (subst-sexp/k new old (car ls)
                    (subst1-cont new old ls k))))

(define (subst-sexp/k new old exp k)
  (if (symbol? exp)
      (apply-cont k
                  (if (eqv? old exp)
                      new
                      exp))
      (subst/k new old exp k)))