
(load "lib.scm")

;;; 2.5
(define (empty-env) '())

(define (extend-env var val env)
  (cons (cons var val) env))

(define (apply-env env var)
  (cond
    ((null? env)
     (report-error 'apply-env "variable ~A not bound" var))
    ((pair? (car env))
     (if (eq? (caar env) var)
       (cdar env)
       (apply-env (cdr env) var)))
    (else (report-error 'apply-env "invalid environment"))))
