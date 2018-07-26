#lang eopl

;;; 2.21

(load "racket-lib.ss")

(define-datatype env env?
  (empty-env)
  (extend-env
   (var symbol?)
   (val scheme-value?)
   (rest env?)))

(define (apply-env e svar)
  (cases env e
    (empty-env ()
               (eopl:error 'apply-env "variable ~A is not bound" svar))
    (extend-env (var val rest)
                (if (eq? var svar)
                    val
                    (apply-env rest svar)))))

(define (has-binding? e svar)
  (cases env e
    (empty-env () #f)
    (extend-env (var val rest)
                (if (eq? var svar)
                    #t
                    (has-binding? rest svar)))))
