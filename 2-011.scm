
(load "lib.scm")

(define (empty-env) '())

(define empty-env? null?)

(define (extend-env var val env)
  (cons (cons (list var) (list val)) env))

(define (apply-env env var)
  (if (empty-env? env)
    (report-error 'apply-env "variable ~A not bound" var)
    (let rec ((vars (caar env))
              (vals (cdar env)))
      (cond
        ((null? vars) (apply-env (cdr env) var))
        ((eq? (car vars) var) (car vals))
        (else (rec (cdr vars) (cdr vals)))))))

(define (extend-env* vars vals env)
  (cons (cons vars vals) env))
