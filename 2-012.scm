
(load "lib.scm")

(define (empty-stack)
  (lambda (n) (report-error 'empty-stack "stack is empty")))

(define (apply-stack stk n)
  (stk n))

(define (push v stk)
  (lambda (n)
    (case n
      ((top) v)
      ((pop) stk))))

(define (top stk)
  (apply-stack stk 'top))

(define (pop stk)
  (apply-stack stk 'pop))
