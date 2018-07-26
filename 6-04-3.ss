#lang eopl

(define (remove-first x ls)
  (remove-first/k x ls
                  (lambda (val)
                    (eopl:printf "end of computation.~%")
                    val)))

(define (remove-first/k x ls k)
  (cond
    [(null? ls)
     (k '())]
    [(eqv? x (car ls))
     (k (cdr ls))]
    [else
     (remove-first/k x
                     (cdr ls)
                     (lambda (val)
                       (k
                        (cons (car ls)
                              val))))]))

(define (list-sum ls)
  (list-sum/k ls
              (lambda (val)
                (eopl:printf "end of computation.~%")
                val)))

(define (list-sum/k ls k)
  (if (null? ls)
      (k 0)
      (list-sum/k (cdr ls)
                  (lambda (val)
                    (k (+ val (car ls)))))))

(define (occurs-free? x exp)
  (occurs-free?/k x exp
                  (lambda (val)
                    (eopl:printf "end of computation.~%")
                    val)))

(define (occurs-free?/k x exp k)
  (cond
    [(symbol? exp)
     (k (eqv? x exp))]
    [(eqv? (car exp) 'lambda)
     (if (eqv? x (caadr exp))
         (k #f)
         (occurs-free?/k x (caddr exp) k))]
    [else
     (occurs-free?/k x (car exp)
                     (lambda (val1)
                       (occurs-free?/k x (cadr exp)
                                       (lambda (val2)
                                         (k (or val1 val2))))))]))

(define (subst new old ls)
  (subst/k new old ls
           (lambda (val)
             (eopl:printf "end of computation.~%")
             val)))

(define (subst/k new old ls k)
  (if (null? ls)
      (k '())
      (subst-sexp/k new old (car ls)
                    (lambda (val1)
                      (subst/k new old (cdr ls)
                               (lambda (val2)
                                 (k (cons val1 val2))))))))

(define (subst-sexp/k new old exp k)
  (if (symbol? exp)
      (k
       (if (eqv? old exp)
           new
           exp))
      (subst/k new old exp k)))