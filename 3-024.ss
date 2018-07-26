#lang eopl

;;; 3.24

(require "lang-proc.ss")

(define fact #<<EOF
let times = proc (x)
              let timesx = proc (maker)
                             proc (y)
                               if zero?(y)
                               then 0
                               else -(((maker maker) -(y,1)), -(0,x))
              in (timesx timesx)
in let fact = proc (x)
                let makefact = proc (make)
                                 proc (x)
                                   if zero?(x)
                                   then 1
                                   else ((times x) ((make make) -(x,1)))
                in ((makefact makefact) x)
   in (fact 10)                
EOF
  )

(define odd-even #<<EOF
let make-odd = proc (make-even)
                 proc (x)
                   if zero?(x)
                   then 0
                   else ((make-even make-even) -(x,1))
in let make-even = proc (make)
                     proc (x)
                       if zero?(x)
                       then 1
                       else ((make-odd make) -(x,1))
   in let odd = (make-odd make-even)
      in let even = (make-even make-even)
         in (even 10)
EOF
  )


#|
(let* ([make-odd (lambda (make-even)
                     (lambda (x)
                       (if (zero? x)
                           0
                           ((make-even make-even) (- x 1)))))]
      [make-even (lambda (make)
                   (lambda (x)
                     (if (zero? x)
                         1
                         ((make-odd make) (- x 1)))))]
      [odd (make-odd make-even)]
      [even (make-even make-even)])
  (do ([i 0 (+ i 1)])
    ((> i 10))
    (eopl:printf "~A: ~A ~A\n" i (odd i) (even i))))
|#