#lang eopl

(require "lang-proc-modules.ss")

(eopl:pretty-print (run "
module equality-maker
interface
((ints: [opaque t
         zero: t
         succ: (t -> t)
         pred: (t -> t)
         is-zero: (t -> bool)])
=> [equal: (from ints take t -> (from ints take t -> bool))])
body
module-proc (ints:[opaque t
                   zero: t
                   succ: (t -> t)
                   pred: (t -> t)
                   is-zero: (t -> bool)])
[type t = from ints take t
 z? = from ints take is-zero
 p = from ints take pred
 equal =
  letrec (t -> bool) f1(x:t) =
   letrec bool f2(y:t) =
    if (z? y) then (z? x)
    else ((f1 (p x)) (p y))
   in f2
  in f1
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

module ints1-from-int
interface [from-int: (int -> from ints1 take t)]
body (from-int-maker ints1)

module ints1-equal
interface [equal: (from ints1 take t -> (from ints1 take t -> bool))]
body (equality-maker ints1)

((from ints1-equal take equal
  (from ints1-from-int take from-int 12))
   (from ints1-from-int take from-int 11))"))