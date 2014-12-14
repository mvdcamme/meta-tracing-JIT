(begin 
  (define (make-tree-node left right value)
    (vector left right value))
  
  (define (new-tree-node v)
    (make-tree-node '() '() v))
  
  (define (left node)
    (vector-ref node 0))
  
  (define (left! node l)
    (vector-set! node 0 l))
  
  (define (right node )
    (vector-ref node 1))
  
  (define (right! node r)
    (vector-set! node 1 r))
  
  (define (value! node vl)
    (vector-set! node 2 vl))
  
  (define (value node )
    (vector-ref node 2))
  
  (define (insert! node n)
    (if (< n (value node))
        (if (null? (left node))
            (left! node (new-tree-node n))
            (insert! (left node) n))
        (if (null? (right node))
            (right! node (new-tree-node n))
            (insert! (right node) n))))
  
  (define (tree-sort vec)
    (if (> (vector-length vec) 1)
        (begin (define n (new-tree-node (vector-ref vec 0)))
               (define (loop i)
                 (if (< i (vector-length vec))
                     (begin (insert! n (vector-ref vec i))
                            (loop (+ i 1)))
                     n))
               (loop 1))
        #f))
  
  (define (make-random-array length)
    (define v (make-vector length))
    (define (loop i)
      (if (< i  length)
          (begin (vector-set! v i (random 1000))
                 (loop (+ i 1)))
          v))
    (loop 0))
  
  (define random-vec (make-random-array 20))
  
  (tree-sort random-vec))