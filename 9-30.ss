#lang eopl

(require "lang-typed-oo.ss")

(test '((16 0)
        (12 10)
        (21 0))
      "
interface summable
 method int sum()

%%%%%%%%%%%%%%%%% summable list %%%%%%%%%%%%%%%%%%

class summable-list extends object implements summable
 field listof int ls
 method void initialize(v: listof int)
  set ls = v
 method int sum()
  send self add(ls)
 method int add(ls: listof int)
  if null?(ls) then 0
  else +(car(ls), send self add(cdr(ls)))

%%%%%%%%%%%%%%%%%%  summable bin tree %%%%%%%%%%%%%%%

class summable-bintree extends object implements summable
 method int initialize() 1
 method int sum() 0

class bin-node extends summable-bintree
 field summable-bintree left
 field summable-bintree right
 method void initialize(l: summable-bintree, r: summable-bintree)
  begin
   set left = l;
   set right = r;
  end
 method int sum()
  +(send left sum(), send right sum())

class bin-leaf extends summable-bintree
 field int value
 method void initialize(v: int) set value = v
 method int sum() value

%%%%%%%%%%%%%%%%%%  summable tree  ;;;;;;;;;;;;;;;

class summable-tree extends object implements summable
 method int initialize() 1
 method int sum() 0

class tree-node extends summable-tree
 field listof summable-tree ls
 method void initialize(v: listof summable-tree)
  set ls = v
 method int sum()
  send self add(ls)
 method int add(ls: listof summable-tree)
  if null?(ls) then 0
  else +(send car(ls) sum(),
         send self add(cdr(ls)))

class tree-leaf extends summable-tree
 field int value
 method void initialize(v: int) set value = v
 method int sum() value

let ls1 = new summable-list(list(1,3,5,7))
    ls2 = new summable-list(null:int)

    bt1 = new bin-node(
           new bin-node(
            new bin-leaf(3),
            new bin-leaf(4)),
           new bin-leaf(5))
    bt2 = new bin-leaf(10)

    t1 = new tree-node(
          list(cast new tree-leaf(1) summable-tree,
               cast new tree-node(
                list(cast new tree-leaf(2) summable-tree,
                     cast new tree-leaf(3) summable-tree,
                     cast new tree-leaf(4) summable-tree)) summable-tree,
               cast new tree-leaf(5) summable-tree,
               cast new tree-node(
                list(cast new tree-leaf(6) summable-tree)) summable-tree))
    t2 = new tree-node(null: summable-tree)
in
list(list(send ls1 sum(),
          send ls2 sum()),
     list(send bt1 sum(),
          send bt2 sum()),
     list(send t1 sum(),
          send t2 sum()))
")