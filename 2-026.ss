#lang eopl

;;; 2.26

(define-datatype rbtree rbtree?
  (red-node
   (left rbtree?)
   (right rbtree?))
  (blue-node
   (son-list (list-of rbtree?)))
  (leaf-node
   (int integer?)))

(define (mark-leaves-with-red-depth rbt)
  (let rec ([rbt rbt]
            [n 0])
    (cases rbtree rbt
      [leaf-node (i)
        (leaf-node n)]
      [red-node (l r)
        (red-node (rec l (+ 1 n)) (rec r (+ 1 n)))]
      [blue-node (lrb)
        (blue-node (map (lambda (t)
                          (rec t n))
                     lrb))])))

(define (rbtree->plain rbt)
  (cases rbtree rbt
    (red-node (l r)
      (list 'red
            (rbtree->plain l)
            (rbtree->plain r)))
    (blue-node (lrb)
      (apply list 'blue (map rbtree->plain lrb)))
    (leaf-node (i)
      (list i))))
