#lang eopl

(require "lang-cps-in-for-ex.ss")

;;; removeall
(run "
letrec removeall(n, s) =
 if null?(s) then null
 else if number?(car(s)) then if equal?(n, car(s)) then (removeall n cdr(s))
                              else cons(car(s), (removeall n cdr(s)))
      else cons((removeall n car(s)),
                (removeall n cdr(s)))
in print((removeall 3 list(2,3,list(1,list(2,3,4),list(3,5)),10,3)))
")

(run "
letrec removeall/k(n, s, k) =
 if null?(s) then (k null)
 else if number?(car(s)) then if equal?(n, car(s)) then (removeall/k n cdr(s) k)
                              else (removeall/k n cdr(s)
                                     proc (val)
                                      (k cons(car(s), val)))
      else (removeall/k n car(s)
             proc (val1)
              (removeall/k n cdr(s)
                 proc (val2)
                  (k cons(val1, val2))))
in (removeall/k 3 list(2,3,list(1,list(2,3,4),list(3,5)),10,3)
           proc (val)
            print(val))
")

;;; occurs-in?
(run "
letrec occurs-in?(n, s) =
 if null?(s) then false
 else if number?(car(s)) then if equal?(n, car(s)) then true
                              else (occurs-in? n cdr(s))
      else if (occurs-in? n car(s)) then true
           else (occurs-in? n cdr(s))
in begin
 print((occurs-in? 3 list(1,2,list(4,16,123),8)));
 print((occurs-in? 3 list(1,list(list(1,3,5),2),23)));
end")

(run "
letrec occurs-in?/k(n, s, k) =
 if null?(s) then (k false)
 else if number?(car(s)) then if equal?(n, car(s)) then (k true)
                              else (occurs-in?/k n cdr(s) k)
      else (occurs-in?/k n car(s)
             proc (val)
              if val then (k true)
              else (occurs-in?/k n cdr(s) k))
in let k = proc (val) print(val)
in begin
 (occurs-in?/k 3 list(1,2,list(4,16,123),8) k);
 (occurs-in?/k 3 list(1,list(list(1,3,5),2),23) k);
end")

;; remfirst
(run "
letrec occurs-in?(n, s) =
 if null?(s) then false
 else if number?(car(s)) then if equal?(n, car(s)) then true
                              else (occurs-in? n cdr(s))
      else if (occurs-in? n car(s)) then true
           else (occurs-in? n cdr(s))
 remfirst(n, s) =
  letrec loop(s) =
   if null?(s) then null
   else if number?(car(s)) then if equal?(n, car(s)) then cdr(s)
                                else cons(car(s), (loop cdr(s)))
        else if (occurs-in? n car(s)) then cons((remfirst n car(s)), cdr(s))
             else cons(car(s), (remfirst n cdr(s)))
 in (loop s)
in begin
 print((remfirst 3 list(1,2,list(list(3,4,6,3),list(1,2,3,4),3),3,4,5)));
 print((remfirst 3 list(1,2,list(list(1),list(1,2,3,4),3),3,4,5)));
end")

(run "
letrec occurs-in?/k(n, s, k) =
 if null?(s) then (k false)
 else if number?(car(s)) then if equal?(n, car(s)) then (k true)
                              else (occurs-in?/k n cdr(s) k)
      else (occurs-in?/k n car(s)
             proc (val)
              if val then (k true)
              else (occurs-in?/k n cdr(s) k))
 remfirst/k(n, s, k) =
  letrec loop(s, k) =
   if null?(s) then (k null)
   else if number?(car(s)) then if equal?(n, car(s)) then (k cdr(s))
                                else (loop cdr(s)
                                       proc (val)
                                        (k cons(car(s), val)))
        else (occurs-in?/k n car(s)
               proc (val)
                if val then (remfirst/k n car(s)
                              proc (val)
                               (k cons(val, cdr(s))))
                else (remfirst/k n cdr(s)
                       proc (val)
                        (k cons(car(s), val))))
 in (loop s k)
in let k = proc (val) print(val)
in begin
 (remfirst/k 3 list(1,2,list(list(3,4,6,3),list(1,2,3,4),3),3,4,5) k);
 (remfirst/k 3 list(1,2,list(list(1),list(1,2,3,4),3),3,4,5) k);
end")

;; depth
(run "
letrec depth(s) =
 if null?(s) then 1
 else if number?(car(s)) then (depth cdr(s))
      else if less?(add1((depth car(s))), (depth cdr(s)))
           then (depth cdr(s))
           else add1((depth car(s)))
in begin
 print((depth list(1,list(1,list(2,3),list(2,list(3)),list(list(list(1)))))));
 print((depth list(1,list(1,list(2,list(2,3)),list(2,3)),1)));
end")

(run "
letrec depth/k(s, k) =
 if null?(s) then (k 1)
 else if number?(car(s)) then (depth/k cdr(s) k)
      else (depth/k car(s)
             proc (val1)
              (depth/k cdr(s)
                proc (val2)
                 if less?(add1(val1), val2) then (k val2)
                 else (k add1(val1))))
in let k = proc (val) print(val)
in begin
 (depth/k list(1,list(1,list(2,3),list(2,list(3)),list(list(list(1))))) k);
 (depth/k list(1,list(1,list(2,list(2,3)),list(2,3)),1) k);
end")


;; map
(run "
letrec map(f, l) =
 if null?(l) then null
 else cons((f car(l)), (map f cdr(l)))
in letrec square(n) = *(n, n)
in print((map square list(1,2,3,4,5)))
")

(run "
letrec map/k(f, l, k) =
 if null?(l) then (k null)
 else (f car(l)
        proc (val1)
         (map/k f cdr(l)
           proc (val2)
            (k cons(val1, val2))))
in letrec square/k(n, k) = (k *(n, n))
in (map/k square/k list(1,2,3,4,5)
    proc (val) print(val))
")

;; fnlrgtn
(run "
letrec fnlrgtn(l, n) =
 if null?(l) then false
 else if number?(car(l)) then if less?(n, car(l)) then car(l)
                              else (fnlrgtn cdr(l) n)
      else let f = (fnlrgtn car(l) n)
           in if number?(f) then f
              else (fnlrgtn cdr(l) n)
in begin
 print((fnlrgtn list(1,list(3,list(2),7,list(9))) 6));
 print((fnlrgtn list(1,list(3,list(2),7,list(9))) 9));
end")

(run "
letrec fnlrgtn/k(l, n, k) =
 if null?(l) then (k false)
 else if number?(car(l)) then if less?(n, car(l)) then (k car(l))
                              else (fnlrgtn/k cdr(l) n k)
      else (fnlrgtn/k car(l) n
             proc (val)
              if number?(val) then (k val)
              else (fnlrgtn/k cdr(l) n k))
in let k = proc(val) print(val)
in begin
 (fnlrgtn/k list(1,list(3,list(2),7,list(9))) 6 k);
 (fnlrgtn/k list(1,list(3,list(2),7,list(9))) 9 k);
end")

;; every
(run "
letrec every(pred, l) =
 if null?(l) then true
 else if (pred car(l)) then (every pred cdr(l))
      else false
in begin
 print((every proc(n)less?(5, n) list(6,7,8,9)));
 print((every proc(n)less?(5, n) list(6,7,5,9)));
end")

(run "
letrec every/k(pred/k, l, k) =
 if null?(l) then (k true)
 else (pred/k car(l)
        proc (val)
         if val then (every/k pred/k cdr(l) k)
         else (k false))
in let k = proc(n)print(n)
in begin
 (every/k proc(n,k)(k less?(5, n)) list(6,7,8,9) k);
 (every/k proc(n,k)(k less?(5, n)) list(6,7,5,9) k);
end")