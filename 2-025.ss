#lang eopl

(define-datatype bintree bintree?
  (leaf-node
   (num integer?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

(define (leaf-num bt)
  (cases bintree bt
    (leaf-node (n) n)
    (else
     (eopl:error 'leaf-num "bintree is not leaf"))))

(define (interior-node? bt)
  (cases bintree bt
    (interior-node (a b c) #t)
    (else #f)))

(define (max-interior bt)
  (letrec ([rec (lambda (bt)
                  (cases bintree bt
                    (leaf-node (n)
                      (eopl:error 'max-interior "bintree is single leaf"))
                    (interior-node (key l r)
                      (let ([li (interior-node? l)]
                            [ri (interior-node? r)])
                        (cond
                          [(and li ri)
                           (let* ([pl (rec l)]
                                  [pr (rec r)]
                                  [total (+ (car pl) (car pr))])
                             (cons total (max-pair (cons total key)
                                                   (cdr pl)
                                                   (cdr pr))))]
                          [(not (or li ri))
                           (let ([total (+ (leaf-num l) (leaf-num r))])
                             (cons total (cons total key)))]
                          [else
                           (let* ([p (rec (if li l r))]
                                  [total (+ (leaf-num (if li r l))
                                           (car p))])
                             (cons total (max-pair (cons total key) (cdr p))))])))))]
           [max-pair (lambda (p1 . p)
                       (if (null? p)
                           p1
                           (let ([max (apply max-pair p)])
                             (if (> (car p1) (car max))
                               p1
                               max))))])
    (cddr (rec bt))))