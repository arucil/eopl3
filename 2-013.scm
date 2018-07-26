
(load "lib.scm")

(define (empty-env)
  (cons
    (lambda (var)
      (report-error 'apply-env "variable ~A not bound" var))
    (lambda () #t)))

(define (extend-env var val env)
  (cons
    (lambda (svar)
      (if (eq? svar var)
        val
        (apply-env env svar)))
    (lambda () #f)))

(define (apply-env env var)
  ((car env) var))

(define (empty-env? env)
  ((cdr env)))
