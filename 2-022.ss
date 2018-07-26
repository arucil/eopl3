#lang eopl

(require "racket-lib.ss")

;;; 2.22

(define-datatype stack stack?
  (empty-stack)
  (push
   (val scheme-value?)
   (rest stack?)))

(define (top stk)
  (cases stack stk
    (empty-stack ()
                 (eopl:error 'top "stack is empty"))
    (push (val rest) val)))

(define (pop stk)
  (cases stack stk
    (empty-stack ()
                 (eopl:error 'pop "stack is empty"))
    (push (val rest) rest)))

(define (empty-stack? stk)
  (cases stack stk
    (empty-stack () #t)
    (else #f)))