(load "lib.scm")

;;; 2.6

;; 1)
;; the environment is represented as:
;;  ( (var_1 var_2 ... var_n) . (val_1 val_2 ... val_n) )
(define (empty-env-1) '(()))

(define (extend-env-1 var val env)
  (cons (cons var (car env)) (cons val (cdr env))))

(define (apply-env-1 env var)
  (let ((i (list-index-from (car env) var 0)))
    (if (not i)
      (report-error 'apply-env "variable ~A not bound" var)
      (list-ref (cdr env) i))))

(define (list-index-from ls x n)
  (cond
    ((null? ls) #f)
    ((eq? (car ls) x) n)
    (else (list-index-from (cdr ls) x (+ n 1)))))

;; 2)
;;   ( var_1 val_1 var_2 val_2 ... var_n val_n )
(define (empty-env-2) '())

(define (extend-env-2 var val env)
  (cons var (cons val env)))

(define (apply-env-2 env var)
  (cond
    ((null? env)
     (report-error 'apply-env "variable ~A not bound" var))
    ((eq? (car env) var) (cadr env))
    (else
      (apply-env-2 (cddr env) var))))

;; 3)
;; BST:
;; ( var val left-child right-child )

(define (empty-env-3) '())

(define (extend-env-3 var val env)
  (if (null? env)
    (list (symbol->string var) val '() '())
    (let ((svar (symbol->string var))
          (s (car env)))
      (cond
        ((string=? svar s)
         (list s val (caddr env) (cadddr env)))
        ((string>? svar s)
         (list s
               (cadr env)
               (caddr env)
               (extend-env-3 var val (cadddr env))))
        (else
          (list s
                (cadr env)
                (extend-env-3 var val (caddr env))
                (cadddr env)))))))

(define (apply-env-3 env var)
  (if (null? env)
    (report-error 'apply-env "variable ~A not bound" var)
    (let ((svar (symbol->string var))
          (s (car env)))
      (cond
        ((string=? svar s) (cadr env))
        ((string>? svar s)
         (apply-env-3 (cadddr env) var))
        (else
          (apply-env-3 (caddr env) var))))))
