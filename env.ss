#lang eopl

(define (empty-env)
  '())

(define (extend-env var val env)
  (cons (cons var val) env))

(define empty-env? null?)

(define (apply-env env svar)
  (cond
    [(null? env)
     (eopl:error 'apply-env "variable ~s is not bound" svar)]
    [(eqv? svar (caar env))
     (cdar env)]
    [else
     (apply-env (cdr env) svar)]))

(define (environment? v)
  (cond
    [(null? v) #t]
    [(pair? v)
     (and (pair? (car v))
          (environment? (cdr v)))]
    [else #f]))

(provide empty-env)
(provide extend-env)
(provide empty-env?)
(provide apply-env)
(provide environment?)