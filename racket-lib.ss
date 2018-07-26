
#lang eopl

(provide scheme-value?)
(provide identifier?)

(define (scheme-value? v) #t)

(define identifier? symbol?)
