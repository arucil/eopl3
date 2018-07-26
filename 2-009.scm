
(load "2-008.scm")

(define (has-binding? env var)
  (cond
    ((empty-env? env) #f)
    ((eq? (caar env) var) #t)
    (else (has-binding? (cdr env) var))))
