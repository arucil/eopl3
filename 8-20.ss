#lang eopl

(require "lang-proc-modules.ss")

(eopl:pretty-print (run "
module sum-prod-maker
interface
((ints: [opaque t
         zero: t
         succ: (t -> t)
         pred: (t -> t)
         is-zero: (t -> bool)])
=> [plus: (from ints take t -> (from ints take t -> from ints take t))
    times: (from ints take t -> (from ints take t -> from ints take t))])
body
module-proc (ints:[opaque t
                   zero: t
                   succ: (t -> t)
                   pred: (t -> t)
                   is-zero: (t -> bool)])
[
 type t = from ints take t
 z? = from ints take is-zero
 z = from ints take zero
 p = from ints take pred
 s = from ints take succ
 plus = proc(x: t)
         letrec t f(y:t) =
          if (z? y) then x
          else (s (f (p y)))
         in f
 times = proc(x: t)
          letrec t f(y:t) =
           if (z? y) then z
           else ((plus (f (p y))) x)
          in f
]

module from-int-maker
interface
((ints: [opaque t
         zero: t
         succ: (t -> t)
         pred: (t -> t)
         is-zero: (t -> bool)])
=> [from-int : (int -> from ints take t)])
body
module-proc (ints:[opaque t
                   zero: t
                   succ: (t -> t)
                   pred: (t -> t)
                   is-zero: (t -> bool)])
[from-int =
  letrec from ints take t f(x:int) =
   if zero?(x) then from ints take zero
   else (from ints take succ (f -(x,1)))
  in f ]

module ints1
interface
[opaque t
 zero: t
 succ: ( t -> t)
 pred: (t -> t)
 is-zero: (t -> bool)
]
body
[type t = int
 zero = 33
 succ = proc(x:t) -(x,-1)
 pred = proc(x:t) -(x,1)
 is-zero = proc(x:t) zero?(-(x,zero))
]

module ints1-sp
interface [plus: (from ints1 take t -> (from ints1 take t -> from ints1 take t))
           times: (from ints1 take t -> (from ints1 take t -> from ints1 take t))]
body (sum-prod-maker ints1)

module ints1-from-int
interface [from-int: (int -> from ints1 take t)]
body (from-int-maker ints1)

letrec int to-int(x: from ints1 take t) =
 if (from ints1 take is-zero x) then 0
 else -((to-int (from ints1 take pred x)), -1)
in
 let plus = from ints1-sp take plus
 in let times = from ints1-sp take times
 in let from-int = from ints1-from-int take from-int
 in
  (to-int ((plus (from-int 11))
           ((times (from-int 3))
            (from-int 17))))"))