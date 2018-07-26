#lang eopl

(require "lang-threads.ss")

(run 4 "
let make-mutex = proc ()
                  let m = mutex()
                  in begin
                      wait(m);
                      m;
                     end
in let m1 = (make-mutex)
       m2 = (make-mutex)
       m3 = (make-mutex)
       mx = mutex()
       x = 0
   in let inc-x = proc (m)
                   proc ()
                    begin
                     wait(mx);
                     set x = -(x, -1);
                     signal(mx);
                     signal(m);
                    end
      in begin
          spawn((inc-x m1));
          spawn((inc-x m2));
          spawn((inc-x m3));
          wait(m1); wait(m2); wait(m3);
          print(x);
         end
")