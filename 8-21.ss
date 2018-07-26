#lang eopl

(require "lang-proc-modules.ss")

(eopl:pretty-print (run "
module k2-maker
interface
((ints: [opaque t
         zero: t
         succ: (t -> t)
         pred: (t -> t)
         is-zero: (t -> bool)])
=> [opaque t
    zero: t
    succ: (t -> t)
    pred: (t -> t)
    is-zero: (t -> bool)])
body
module-proc (ints:[opaque t
                   zero: t
                   succ: (t -> t)
                   pred: (t -> t)
                   is-zero: (t -> bool)])
[type t = from ints take t
 s = from ints take succ
 p = from ints take pred
 z? = from ints take is-zero
 z = from ints take zero
 zero = z
 succ = proc(x: t) (s (s x))
 pred = proc(x: t) (p (p x))
 is-zero = z?
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

module ints1-k2
interface
[opaque t
 zero: t
 succ: ( t -> t)
 pred: (t -> t)
 is-zero: (t -> bool)
]
body
(k2-maker ints1)

module ints1-k2-from-int
interface [from-int: (int -> from ints1-k2 take t)]
body (from-int-maker ints1-k2)

letrec int to-int(x: from ints1-k2 take t) =
 if (from ints1-k2 take is-zero x) then 0
 else -((to-int (from ints1-k2 take pred x)), -1)
in
  (to-int (from ints1-k2-from-int take from-int 10))"))