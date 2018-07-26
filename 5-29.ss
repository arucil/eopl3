#lang eopl

(define n 0)
(define acc 0)

(define (fact-iter)
  (set! acc 1)
  (fact-iter-acc))

(define (fact-iter-acc)
  (unless (zero? n)
        (set! acc (* acc n))
        (set! n (- n 1))
        (fact-iter-acc)))

(set! n 10)
(fact-iter)
(display acc)