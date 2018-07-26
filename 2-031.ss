#lang eopl

(define-datatype prefix-exp prefix-exp?
  (const-exp
   (num integer?))
  (diff-exp
   (operand1 prefix-exp?)
   (operand2 prefix-exp?)))

(define (parse-prefix-exp v)
  (letrec ([rec (lambda (v)
                  (cond
                    [(integer? (car v))
                     (cons (const-exp (car v))
                           (cdr v))]
                    [(eq? (car v) '-)
                     (let* ([op1 (rec (cdr v))]
                            [op2 (rec (cdr op1))])
                       (cons (diff-exp (car op1)
                                       (car op2))
                             (cdr op2)))]))])
    (car (rec v))))