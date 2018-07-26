#lang eopl

(require "lang-proc-modules.ss")

(eopl:pretty-print (run "
module table-of
interface
((val:[opaque t
       default: t])
 =>
 [opaque table
  empty: table
  add-to-table: (int -> (from val take t -> (table -> table)))
  lookup-in-table: (int -> (table -> from val take t))])
body
module-proc (val:[opaque t
                  default: t])
[type t = from val take t
 type table = (int -> t)
 empty = proc(x:int) from val take default
 add-to-table = proc(var:int)
                 proc(val:t)
                  proc(t:table)
                   proc(x:int)
                    if zero?(-(x,var)) then val
                    else (t x)
 lookup-in-table = proc(var:int)
                    proc(t:table)
                     (t var)
]

module mybool
interface
[opaque t
 true: t
 false: t
 default: t
 to-bool: (t -> bool)
 and: (t -> (t -> t))
 ]
body
[type t = int
 true = 0
 false = 13
 default = false
 to-bool = proc(x:t) zero?(x)
 and = proc(x:t) proc(y:t) if zero?(x) then y else false
]

module mybool-table
interface
[opaque table
 empty: table
 add-to-table: (int -> (from mybool take t -> (table -> table)))
 lookup-in-table: (int -> (table -> from mybool take t))]
body (table-of mybool)

let and = from mybool take and
in let true = from mybool take true
in let false = from mybool take false
in let to-bool = from mybool take to-bool
in let extend = from mybool-table take add-to-table
in let apply = from mybool-table take lookup-in-table
in let empty = from mybool-table take empty
in let t1 = (((extend 3) false)
             (((extend 4) true)
              (((extend 3) true)
               empty)))
in (to-bool ((and ((apply 3) t1))
             ((apply 4) t1)))
"))