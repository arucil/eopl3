#lang eopl

(define (list-sum ls)
  (list-sum/k ls 0))

(define (list-sum/k ls k)
  (if (null? ls)
      k
      (list-sum/k (cdr ls)
                  (+ k (car ls)))))