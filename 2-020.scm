
(load "lib.scm")

;;; 2.20

;; bintree-parent-son ::=  (int parent left-child right-child) | ( () parent )
;; parent ::= ( int_p dir_p dir_p_other_child ... )
;; dir ::= left | right
;;
;; child ::= (int left-child right-child) | ()

(define (number->bintree n)
  (list n '() '() '()))

(define (at-leaf? tree)
  (null? (current-element tree)))

(define is-leaf? null?)

(define parent cadr)

(define current-element car)

(define lson caddr)

(define rson cadddr)

(define par-element car)

(define par-dir cadr)

(define par-son caddr)

(define par-left cdddr)

(define son-element car)

(define son-lson cadr)

(define son-rson caddr)

(define (insert-to-left n tree)
  (list (current-element tree)
        (parent tree)
        (list n (lson tree) '())
        (rson tree)))

(define (insert-to-right n tree)
  (list (current-element tree)
        (parent tree)
        (lson tree)
        (list n '() (rson tree))))

(define (move-to-left-son tree)
  (if (at-leaf? tree)
    (report-error 'move-to-left-son "tree at leaf")
    (let ((lson (lson tree))
          (newp (list* (current-element tree)
                       'left
                       (rson tree)
                       (parent tree))))
      (if (is-leaf? lson)
        (list '() newp)
        (list (son-element lson)
              newp
              (son-lson lson)
              (son-lson lson))))))

(define (move-to-right-son tree)
  (if (at-leaf? tree)
    (report-error 'move-to-riht-son "tree at leaf")
    (let ((rson (rson tree))
          (newp (list* (current-element tree)
                       'right
                       (lson tree)
                       (parent tree))))
      (if (is-leaf? rson)
        (list '() newp)
        (list (son-element rson)
              newp
              (son-lson rson)
              (son-rson rson))))))

(define (at-root? tree)
  (null? (parent tree)))

(define (move-up tree)
  (if (at-root? tree)
    (report-error 'move-up "tree at root")
    (let ((p (parent tree))
          (newson (if (at-leaf? tree)
                    '()
                    (list (current-element tree)
                          (lson tree)
                          (rson tree)))))
      (case (par-dir p)
        ((left)
         (list (par-element p)
               (par-left p)
               newson
               (par-son p)))
        ((right)
         (list (par-element p)
               (par-left p)
               (par-son p)
               newson))))))

;; parent-son representation to plain bintree
(define (bintree->plain tree)
  (if (at-root? tree)
    (list (current-element tree)
          (lson tree)
          (rson tree))
    (bintree->plain (move-up tree))))
