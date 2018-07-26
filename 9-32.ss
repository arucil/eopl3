#lang eopl

(require "lang-typed-oo.ss")

(test '(100 200)
      "
interface tree
 method int sum()
 method bool equal(t:tree)
 method bool equal/data(id:int, data:data)

class data extends object
 field node node
 field leaf leaf
 method int initialize() 1
 method void setnode(t:node) set node = t
 method void setleaf(t:leaf) set leaf = t
 method node node() node
 method leaf leaf() leaf

class node extends object implements tree
 field tree left
 field tree right
 method void initialize(l:tree, r:tree)
  begin
   set left = l;
   set right = r;
  end
 method tree left() left
 method tree right() right
 method int sum() +(send left sum(), send right sum())
 method bool equal(t:tree)
  let d = new data()
  in begin
      send d setnode(self);
      send t equal/data(10, d);
     end
 method bool equal/data(id:int, d:data)
  if equal?(id, 10)
  then send send d node() node-equal(self)
  else zero?(1)
 method bool node-equal(t:node)
  if send left equal(send t left())
  then send right equal(send t right())
  else zero?(1)

class leaf extends object implements tree
 field int value
 method void initialize(v:int) set value = v
 method int sum() value
 method int value() value
 method bool equal(t:tree)
  let d = new data()
  in begin
      send d setleaf(self);
      send t equal/data(100, d);
     end
 method bool equal/data(id:int, d:data)
  if equal?(id, 100)
  then send send d leaf() leaf-equal(self)
  else zero?(1)
 method bool leaf-equal(t:leaf)
  equal?(value, send t value())

let o1 = new node(
         new node(
          new leaf(3),
          new leaf(4)),
         new leaf(5))
    o2 = new node(
          new node(
           new node(
            new leaf(1),
            new leaf(2)),
           new leaf(4)),
          new leaf(5))
in list(if send o1 equal(o1) then 100 else 200,
        if send o1 equal(o2) then 100 else 200)
")