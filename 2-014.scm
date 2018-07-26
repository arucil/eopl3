
(load "lib.scm")

(define (empty-env)
  (list
    (lambda (var)
      (report-error 'apply-env "variable ~A not bound" var))
    (lambda () #t)
    (lambda (var) #f)))

(define (extend-env var val env)
  (list
    (lambda (svar)
      (if (eq? svar var)
        val
        (apply-env env svar)))
    (lambda () #f)
    (lambda (svar)
      (if (eq? svar var)
        #t
        (has-binding? env svar)))))

(define (apply-env env var)
  ((car env) var))

(define (empty-env? env)
  ((cadr env)))

(define (has-binding? env var)
  ((caddr env) var))
