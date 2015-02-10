(begin
  
  (define MAX_ITERATIONS 10)
  
  (define (vector-map f v)
    (define length (vector-length v))
    (define new-vector (make-vector length))
    (define (loop i)
      (if (< i length)
          (begin (vector-set! new-vector i (f (vector-ref v i)))
                 (loop (+ i 1)))))
    (loop 0)
    new-vector)
  
  (define (make-code)
    (define fun #f)
    (set! fun (eval '(begin (define (f)
                              (define (loop i)
                                (if (< i 300000000)
                                    (loop (+ i 1))
                                    '()))
                              (loop 0))
                            f)))
    fun)
  
  (define N 593)      ; prime number
  
  (define codes (vector-map (lambda (ignored)
                              (make-code))
                            (make-vector N)))
  
  (define (main-function)
    (define step (+ (random N) 1))
    (define i 0)
    (define (loop it)
      (if (< it MAX_ITERATIONS)
        (begin ((vector-ref codes (modulo i N)))
               (set! i (+ i step))
               (loop (+ it 1)))))
    (loop 0))
  
  (main-function))