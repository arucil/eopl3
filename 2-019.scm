
(load "lib.scm")

;;; 2.19

(define (number->bintree n)
  (list n '() '()))

(define at-leaf? null?)

(define (current-element tree)
  (if (at-leaf? tree)
    (report-error 'current-element "tree at leaf")
    (car tree)))

(define (move-to-left-son tree)
  (if (at-leaf? tree)
    (report-error 'move-to-left-son "tree at leaf")
    (cadr tree)))

(define (move-to-right-son tree)
  (if (at-leaf? tree)
    (report-error 'move-to-right-son "tree at leaf")
    (caddr tree)))

(define (insert-to-left n tree)
  (list (car tree)
        (list n (cadr tree) '())
        (caddr tree)))

(define (insert-to-right n tree)
  (list (car tree)
        (cadr tree)
        (list n '() (caddr tree))))


