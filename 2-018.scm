
(load "lib.scm")

;;; 2.18

(define (number->sequence n)
  (list n '() '()))

(define (current-element seq)
  (car seq))

(define (move-to-left seq)
  (if (at-left-end? seq)
    (report-error 'move-to-left "sequence at left end")
    (list (caadr seq)
          (cdadr seq)
          (cons (car seq) (caddr seq)))))

(define (move-to-right seq)
  (if (at-right-end? seq)
    (report-error 'move-to-eight "sequence at right end")
    (list (caaddr seq)
          (cons (car seq) (cadr seq))
          (cdaddr seq))))

(define (insert-to-left n seq)
  (list (car seq)
        (cons n (cadr seq))
        (caddr seq)))

(define (insert-to-right n seq)
  (list (car seq)
        (cadr seq)
        (cons n (caddr seq))))

(define (at-left-end? seq)
  (null? (cadr seq)))

(define (at-right-end? seq)
  (null? (caddr seq)))
