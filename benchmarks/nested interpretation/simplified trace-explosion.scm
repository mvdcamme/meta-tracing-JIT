(begin (define (loop n)
         (if (= (random 2) 0)
             (begin (display "f 0") (newline))
             (begin (display "f 1") (newline)))
         (if (= (random 2) 0)
             (begin (display "g 0") (newline))
             (begin (display "g 1") (newline)))
         (if (= (random 2) 0)
             (begin (display "h 0") (newline))
             (begin (display "h 1") (newline)))
         (if (> n 0)
             (begin (loop (- n 1)))))
       (loop 3))