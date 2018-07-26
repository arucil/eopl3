#lang eopl

(require "racket-lib.ss")

(define-datatype lc-exp lc-exp?
  (var-exp
   (var identifier?))
  (lambda-exp
   (bound-var identifier?)
   (body lc-exp?))
  (app-exp
   (rator lc-exp?)
   (rand lc-exp?)))

(define (report-invalid-concrete-syntax-error datum)
  (eopl:error 'parse-expression "invalid concrete syntax ~A" datum))

(define (parse-expression datum)
  (cond
    [(symbol? datum)
     (var-exp datum)]
    [(and (list? datum) (pair? datum))
     (if (eq? (car datum) 'lambda)
         (if (or (null? (cdr datum))
                 (not (list? (cadr datum)))
                 (null? (cadr datum))
                 (not (identifier? (caadr datum)))
                 (not (null? (cdadr datum)))
                 (null? (cddr datum))
                 (not (null? (cdddr datum))))
             (report-invalid-concrete-syntax-error datum)
             (lambda-exp (caadr datum)
                         (parse-expression (caddr datum))))
         (if (or (null? (cdr datum))
                 (not (null? (cddr datum))))
             (report-invalid-concrete-syntax-error datum)
             (app-exp (parse-expression (car datum))
                      (parse-expression (cadr datum)))))]
    [else (report-invalid-concrete-syntax-error datum)]))