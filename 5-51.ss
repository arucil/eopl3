#lang eopl

(require "lang-threads.ss")

(run 10 "
let buffer = 0
    m = let m1 = mutex()
        in begin
             wait(m1);
             m1;
           end
in let producer = proc (n)
                    letrec wait1(k) =
                             if zero?(k)
                             then begin
                                    set buffer = n;
                                    signal(m);
                                  end
                             else begin
                                    print(2, k);
                                    (wait1 -(k,1));
                                  end
                    in (wait1 10)
       consumer = proc ()
                    begin
                      if zero?(buffer) then wait(m) else 0;
                      buffer;
                    end
in begin
     spawn(proc () (producer 44));
     print(3);
     print((consumer));
end")