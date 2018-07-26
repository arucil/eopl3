
(load "lib.scm")

;;; 2.7

(define (empty-env) '(empty-env))

(define (extend-env var val env)
  (list 'extend-env var val env))

(define (apply-env env var)
  (let rec ((e env))
    (case (car e)
      ((empty-env)
       (report-error 'apply-env "variable ~A not bound in ~A" var env))
      ((extend-env)
       (if (eq? (cadr e) var)
         (caddr e)
         (rec (cadddr e))))
      (else
        (report-error 'apply-env "invalid environment ~A" env)))))
