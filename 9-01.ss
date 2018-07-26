#lang eopl

(require "lang-classes.ss")

(run "
class queue extends object
 field q
 method initialize() set q = null
 method enqueue(x)
  letrec f(ls) =
   if null?(ls) then list(x)
   else cons(car(ls), (f cdr(ls)))
  in set q = (f q)
 method dequeue()
  let x = car(q)
  in begin
      set q = cdr(q);
      x;
     end
 method empty?() null?(q)
let q = new queue()
in
begin
 print(send q empty?());
 send q enqueue(1);
 send q enqueue(2);
 print(list(send q dequeue(), send q empty?()));
 print(list(send q dequeue(), send q empty?()));
end")

(run "
class queue/t extends object
 field q
 field t
 method initialize()
  begin
   set q = null;
   set t = 0;
  end
 method enqueue(x)
  letrec f(ls) =
   if null?(ls) then list(x)
   else cons(car(ls), (f cdr(ls)))
  in begin
      set q = (f q);
      set t = +(t, 1);
     end
 method dequeue()
  let x = car(q)
  in begin
      set q = cdr(q);
      set t = +(t, 1);
      x;
     end
 method empty?() null?(q)
 method tally() t
let q = new queue/t()
in
begin
 print(list(send q empty?(), send q tally()));
 send q enqueue(1);
 send q enqueue(2);
 print(list(send q dequeue(), send q empty?(), send q tally()));
 print(list(send q dequeue(), send q empty?(), send q tally()));
end")

(run "
class tally extends object
 field t
 method initialize() set t = 0
 method count() set t = +(t, 1)
 method tally() t
class queue/gt extends object
 field q
 field t
 method initialize(gt)
  begin
   set q = null;
   set t = gt;
  end
 method enqueue(x)
  letrec f(ls) =
   if null?(ls) then list(x)
   else cons(car(ls), (f cdr(ls)))
  in begin
      set q = (f q);
      send t count();
     end
 method dequeue()
  let x = car(q)
  in begin
      set q = cdr(q);
      send t count();
      x;
     end
 method empty?() null?(q)
 method tally() send t tally()
let t = new tally()
in let q1 = new queue/gt(t)
       q2 = new queue/gt(t)
in
begin
 print(list(send q1 tally(), send q2 tally()));
 send q1 enqueue(1);
 send q1 enqueue(2);
 send q2 enqueue(3);
 send q2 enqueue(4);
 print(list(send q1 dequeue(), send q1 tally(), send q2 tally()));
 print(list(send q2 dequeue(), send q1 tally(), send q2 tally()));
end")