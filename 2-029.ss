#lang eopl

(require "racket-lib.ss")

(define-datatype lc-exp lc-exp?
  (var-exp
   (var identifier?))
  (lambda-exp
   (bound-vars (list-of identifier?))
   (body lc-exp?))
  (app-exp
   (rator lc-exp?)
   (rands (list-of lc-exp?))))

(define (parse-lc-exp v)
  (cond
    [(symbol? v)
     (var-exp v)]
    [(pair? v)
     (if (eq? (car v) 'lambda)
         (lambda-exp (cadr v)
                     (parse-lc-exp (caddr v)))
         (app-exp (parse-lc-exp (car v))
                  (map parse-lc-exp (cdr v))))]
    [else (eopl:error 'parse-lc-exp "invalid concrete syntax")]))