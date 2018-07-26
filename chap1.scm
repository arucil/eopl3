(load "lib.scm")

;; 1.7
;; list  int -> value
;; get n-th element from list l, indexed from 0
(define (nth-element l n)
  (let loop ((ls l) (t n))
    (cond
      ((null? ls) (report-error 'nth-element "~A does not have ~A elements.~\n" l (+ n 1)))
      ((zero? t) (car ls))
      (else (loop (cdr ls) (- t 1))))))

;; 1.9
;; symbol  list -> list
;; remove all occurrences of symbol s from list l, return the result list
(define (remove-all s l)
  (cond
    ((null? l) '())
    ((eq? (car l) s) (remove-all s (cdr l)))
    (else (cons (car l) (remove-all s (cdr l))))))

;; 1.12
(define (my-subst new old l)
  (if (null? l) '()
    (cons
      (if (symbol? (car l))
        (if (eq? (car l) old)
          new
          (car l))
        (my-subst new old (car l)))
      (my-subst new old (cdr l)))))

;;; 1.13
(define (my-subst-map new old l)
  (map (lambda (x)
         (my-subst-sexp new old x))
       l))

(define (my-subst-map-sexp new old l)
  (if (list? l)
    (my-subst-map new old l)
    (if (eq? l old)
      new
      l)))

;; 1.15
;; int value -> list
;; return a list containing n copies of x
(define (duple n x)
  (if (zero? n)
    '()
    (cons x (duple (- n 1) x))))

;; 1.16
;; list -> list
;; return a list with 2-list reversed
(define (invert lst)
  (if (null? lst)
    '()
    (cons (list (cadar lst) (caar lst))
          (invert (cdr lst)))))

;; 1.17
;; list -> list
;; wrap parentheses around each top-level element of list
(define (down lst)
  (if (null? lst)
    '()
    (cons (list (car lst))
          (down (cdr lst)))))

;; 1.18
;; symbol symbol list -> list
(define (swapper s1 s2 slist)
  (if (null? slist)
   '()
   (cons
     (cond
       ((eq? (car slist) s1) s2)
       ((eq? (car slist) s2) s1)
       ((list? (car slist))
        (swapper s1 s2 (car slist)))
       (else (car slist)))
     (swapper s1 s2 (cdr slist)))))

;; 1.19
;; list int value -> list
(define (list-set lst n x)
  (if (null? lst)
    '()
    (cons
      (cond
        ((zero? n) x)
        (else (car lst)))
      (list-set (cdr lst) (- n 1) x))))

;; 1.20
;; symbol list -> int
(define (count-occurrences s slist)
  (if (null? slist)
    0
    (+
      (cond
        ((symbol? (car slist))
         (if (eq? s (car slist))
           1
           0))
        (else (count-occurrences s (car slist))))
      (count-occurrences s (cdr slist)))))

;; 1.21
(define (product sos1 sos2)
  (if (null? sos1)
    '()
    (product-element
      (car sos1)
      sos2
      (product (cdr sos1) sos2))))

(define (product-element s sos2 l)
  (if (null? sos2)
    l
    (cons (list s (car sos2))
          (product-element s (cdr sos2) l))))

;; 1.22
(define (filter-in pred lst)
  (if (null? lst)
    '()
    (if (pred (car lst))
      (cons (car lst)
            (filter-in pred (cdr lst)))
      (filter-in pred (cdr lst)))))

;; 1.23
(define (list-index pred lst)
  (list-index-num pred lst 0))

(define (list-index-num pred lst n)
  (cond
    ((null? lst) #f)
    ((pred (car lst)) n)
    (else (list-index-num pred (cdr lst) (+ n 1)))))

;; 1.24
(define (every? pred lst)
  (cond
    ((null? lst) #t)
    ((not (pred (car lst))) #f)
    (else (every? pred (cdr lst)))))

;; 1.25
(define (exists? pred lst)
  (cond
    ((null? lst) #f)
    ((pred (car lst)) #t)
    (else (exists? pred (cdr lst)))))

;; 1.26
(define (up lst)
  (if (null? lst)
    '()
    ((if (list? (car lst))
       up-element
       cons)
     (car lst)
     (up (cdr lst)))))

(define (up-element lst l)
  (if (null? lst)
    l
    (cons (car lst)
          (up-element (cdr lst) l))))

;; 1.27
(define (flatten slist)
  (flatten-aux slist '()))

(define (flatten-aux slist l)
  (if (null? slist)
     l
     ((if (list? (car slist))
        flatten-aux
        cons)
      (car slist)
      (flatten-aux (cdr slist) l))))

;; 1.28
(define (merge loi1 loi2)
  (cond
    ((null? loi1) loi2)
    ((null? loi2) loi1)
    ((< (car loi1) (car loi2))
     (cons (car loi1)
           (merge (cdr loi1) loi2)))
    (else (cons
            (car loi2)
            (merge loi1 (cdr loi2))))))

;; 1.29
(define (sort loi)
  (let ((i (quotient (length loi) 2)))
    (if (zero? i)
      loi
      (apply merge
             (map sort
                  (sort-split i loi '()))))))

(define (sort-split n lst r)
  (if (zero? n)
    (list lst r)
    (sort-split (- n 1)
                (cdr lst)
                (cons (car lst) r))))

;; 1.30
(define (sort/predicate pred loi)
  (let ((i (quotient (length loi) 2)))
    (if (zero? i)
      loi
      (apply merge/predicate pred
             (map (lambda (l)
                    (sort/predicate pred l))
                  (sort-split i loi '()))))))

(define (merge/predicate pred loi1 loi2)
  (cond
    ((null? loi1) loi2)
    ((null? loi2) loi1)
    ((pred (car loi1) (car loi2))
     (cons (car loi1)
           (merge/predicate pred (cdr loi1) loi2)))
    (else (cons (car loi2)
                (merge/predicate pred loi1 (cdr loi2))))))

;;; 1.31
;; int -> tree
(define (leaf i)
  i)

;; symbol bintree bintree -> bintree
(define interior-node list)

(define leaf? number?)

(define lson cadr)

(define rson caddr)

(define (contents-of tree)
  (if (leaf? tree)
    tree
    (car tree)))

;;; 1.32
(define (double-tree tree)
  (if (leaf? tree)
    (leaf (* 2 (contents-of tree)))
    (interior-node (contents-of tree)
                   (double-tree (lson tree))
                   (double-tree (rson tree)))))

;;; 1.33
(define (mark-leaves-with-red-depth tree)
  (mark-leaves-with-red-depth-from tree 0))

(define (mark-leaves-with-red-depth-from tree n)
  (if (leaf? tree)
    (leaf n)
    (let* ((s (contents-of tree))
           (i (if (eq? s 'red)
               (+ n 1)
               n)))
      (interior-node s
                     (mark-leaves-with-red-depth-from (lson tree) i)
                     (mark-leaves-with-red-depth-from (rson tree) i)))))

;;; 1.34
(define (path n tree)
  (if (null? tree)
    #f
    (let ((t (car tree)))
      (if (= t n)
        '()
        (let ((r (path n
                   ((if (> n t)
                        rson
                        lson)
                    tree))))
          (and r
               (cons (if (> n t)
                       'right
                       'left)
                     r)))))))


;;; 1.35
(define (number-leaves tree)
  (letrec ((rec
             (lambda (n tree)
               (if (leaf? tree)
                 (cons (+ n 1) n)
                 (let* ((l (rec n (lson tree)))
                        (r (rec (car l) (rson tree))))
                   (cons (car r)
                         (interior-node (contents-of tree)
                                        (cdr l)
                                        (cdr r))))))))
    (cdr (rec 0 tree))))

;;; 1.36
(define (g a ls)
  (cons a (map (lambda (l)
                 (cons (+ 1 (car l)) (cdr l)))
               ls)))

(define (number-elements lst)
  (if (null? lst) '()
    (g (list 0 (car lst)) (number-elements (cdr lst)))))
