(begin (define (fac x)
         (if (< x 2)
             1
             (* x (fac (- x 1)))))
       (fac 2))