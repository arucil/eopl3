
;;; 2.3
(define (zero) '(diff (one) (one)))

(define (successor n)
  (list 'diff
        n
        '(diff (diff (one) (one))
               (one))))

(define (predecessor n)
  (list 'diff n '(one)))

(define (diff-tree->integer tree)
  (if (eq? (car tree) 'one)
    1
    (- (diff-tree->integer (cadr tree))
       (diff-tree->integer (caddr tree)))))

(define (is-zero? n)
  (zero? (diff-tree->integer tree)))

(define (diff-tree-plus x y)
  (list 'diff
        x
        (list 'diff
              '(diff (one) (one))
              y)))
