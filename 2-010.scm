
(load "2-009.scm")

(define (extend-env* var-ls val-ls env)
  (if (null? var-ls)
    env
    (extend-env* (cdr var-ls)
                 (cdr val-ls)
                 (extend-env (car var-ls)
                             (car val-ls)
                             env))))
