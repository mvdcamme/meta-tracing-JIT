;;; PNPOLY - Test if a point is contained in a 2D polygon.

(begin
  (define (pt-in-poly2 xp yp x y)
    (define (loop c i j)
      (if (< i 0)
          c
          (if (or (and (or (> (list-ref yp i) y)
                           (>= y (list-ref yp j)))
                       (or (> (list-ref yp j) y)
                           (>= y (list-ref yp i))))
                  (>= x
                      (+ (list-ref xp i)
                         (/ (*
                             (- (list-ref xp j)
                                (list-ref xp i))
                             (- y (list-ref yp i)))
                            (- (list-ref yp j)
                               (list-ref yp i))))))
              (loop c (- i 1) i)
              (loop (not c) (- i 1) i))))
    (loop #f (- (length xp) 1) 0))
	
	(define (run)
	  (let* ((count 0)
                 (xp '(0. 1. 1. 0. 0. 1. -.5 -1. -1. -2. -2.5
                          -2. -1.5 -.5 1. 1. 0. -.5 -1. -.5))
                 (yp '(0. 0. 1. 1. 2. 3. 2. 3. 0. -.5 -1.
                          -1.5 -2. -2. -1.5 -1. -.5 -1. -1. -.5)))
	    (if (pt-in-poly2 xp yp .5 .5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp .5 1.5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -.5 1.5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp .75 2.25) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp 0. 2.01) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -.5 2.5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -1. -.5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -1.5 .5) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -2.25 -1.) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp .5 -.25) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp .5 -1.25) (set! count (+ count 1)))
	    (if (pt-in-poly2 xp yp -.5 -2.5) (set! count (+ count 1)))
	    count))

(run))