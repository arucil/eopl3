#lang eopl

;;; 3.23

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