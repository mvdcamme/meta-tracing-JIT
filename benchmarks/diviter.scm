;;; DIVITER -- Gabriel Benchmark which divides by 2 using lists of n ()'s.
 
(let*
 ((create-n (lambda (n)
              (do ((n n (- n 1))
                   (a '() (cons '() a)))
                ((= n 0) a))))
  (*ll* (create-n 200))
  (iterative-div2 (lambda (l)
                    (do ((l l (cddr l))
                         (a '() (cons (car l) a)))
                      ((null? l) a)))))
  (iterative-div2 *ll*))
