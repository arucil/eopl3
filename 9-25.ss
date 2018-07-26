#lang eopl

;;; use instanceof
(require "9-06.ss")

(test (make-list
       (list
        (bool-val #t)
        (bool-val #f)
        (bool-val #t)
        (bool-val #f)

        (bool-val #t)
        (bool-val #f)
        (bool-val #t)
        (bool-val #f)
        (bool-val #f)
        (bool-val #f)))
      "
class point extends object
 field x
 field y
 method initialize(x1, y1)
  begin
   set x = x1;
   set y = y1;
  end
 method getx() x
 method gety() y
 method similarpoints(pt)
  if equal?(send pt getx(), x)
  then equal?(send pt gety(), y)
  else zero?(1)

class colorpoint extends point
 field color
 method initialize(x, y, c)
  begin
   super initialize(x, y);
   set color = c;
  end
 method getcolor() color
 method similarpoints(pt)
  if super similarpoints(pt)
  then if instanceof pt colorpoint
       then equal?(send pt getcolor(), color)
       else zero?(0)
  else zero?(1)

let p1 = new point(1, 1)
    p2 = new point(1, 2)
    cp1 = new colorpoint(1, 1, 10)
    cp2 = new colorpoint(1, 2, 10)
    cp3 = new colorpoint(1, 1, 20)
    cp4 = new colorpoint(1, 2, 20)
in
list(send p1 similarpoints(p1),
     send p1 similarpoints(p2),
     send p1 similarpoints(cp1),
     send p1 similarpoints(cp2),
     send cp1 similarpoints(p1),
     send cp1 similarpoints(p2),
     send cp1 similarpoints(cp1),
     send cp1 similarpoints(cp2),
     send cp1 similarpoints(cp3),
     send cp1 similarpoints(cp4))
")
