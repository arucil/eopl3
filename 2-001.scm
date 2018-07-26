
;;; 2.1
(define N 16)

(define (zero) '())

(define is-zero? null?)

(define (successor n)
  (cond
    ((is-zero? n) '(1))
    ((= (- N 1) (car n)) (cons 0 (successor (cdr n))))
    (else (cons (+ (car n) 1) (cdr n)))))

(define (predecessor n)
  (cond
    ((and (= (car n) 1) (is-zero? (cdr n))) '())
    ((zero? (car n)) (cons (- N 1) (predecessor (cdr n))))
    (else (cons (- (car n) 1) (cdr n)))))

(define (plus x y)
  (if (is-zero? x)
    y
    (successor (plus (predecessor x) y))))

(define (times x y)
  (if (is-zero? x)
    (zero)
    (plus y (times (predecessor x) y))))

(define (factorial n)
  (if (is-zero? n)
    (successor (zero))
    (times n (factorial (predecessor n)))))

