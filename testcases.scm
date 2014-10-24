;
;test-cases
;

#|

;1
;meta-trace
(define (fac x) (if (< x 2) 1 (* x (fac (- x 1)))))

;2
;regular-trace
(run (inject '(begin (define (f x) (+ x 10))
                       (define (g y) (* y 10))
                       (define (loop h i k)
                         (can-start-loop 'label "loop")
                         (display (h k)) (newline)
                         (if (< i 0)
                             99
                             (loop g (- i 1) k)))
                       (loop f 0 9)
                       (loop f 0 9))))

;3
;regular-trace
(run (inject '(begin (define (fac x)
                       (can-start-loop 'label "fac")
                         (if (< x 2)
                             1
                             (* x (fac (- x 1)))))
                         (fac 5))))

;4
;regular-trace
(run (inject '(begin (define (f x) (+ x 10))
                     (define (g y) (* y 10))
                     (define (loop i k)
                       (can-start-loop 'label "loop")
                       (display ((if (even? i) f g) k)) (newline)
                       (if (< i 0)
                           99
                           (loop (- i 1) k)))
                     (loop 10 9))))


;5
;regular-trace/meta-trace

;
; N-Queens (source: http://c2.com/cgi/wiki?EightQueensInManyProgrammingLanguages)
;

(run (inject '(begin 
 (define (make-queen row col) (list row col))
 (define (get-row queen) (car queen))
 (define (get-col queen) (cadr queen))

 (define (same-row? nq oq) (= (get-row nq) (get-row oq)))
 (define (same-col? nq oq) (= (get-col nq) (get-col oq)))
 (define (same-diag? nq oq)
   (= (abs (- (get-row nq) (get-row oq)))
      (abs (- (get-col nq) (get-col oq)))))

 (define (attacks? nq oq)
   (or (same-row? nq oq) (same-col? nq oq) (same-diag? nq oq)))

 (define (safe? target queens)
   (cond ((null? queens) #t)
         ((attacks? target (car queens)) #f)
         (else (safe? target (cdr queens)))))

 ; Solve for a board size of sz.
 (define (solve sz)
   (define (s-rec sz x y pos sols)
     (display (cons x y)) (newline)
     (cond 
       ; If we've advanced past the last column, we have a solution.
       ; (By the way, the reverse is because pos is built up backward.)
       ((> x sz) (cons (reverse pos) sols))
       ; If we've advanced past the last row, we have a failure.
       ((> y sz) sols)
       ; If the queen is safe, the fun begins.
       ((safe? (make-queen x y) pos)
        ; This is the backtracking call. This is executed once
        ; the inner call is complete.
        (s-rec sz x (+ y 1) pos
               ; Run the next column first; if any solutions
               ; result, they need to be passed to the backtracked
               ; call.
               (s-rec sz (+ x 1) 1
                      ; Add this queen when considering the next
                      ; column's placement.
                      (cons (make-queen x y) pos)
                      sols)))
       ; If this queen isn't safe, move on to the next row.
       (else (s-rec sz x (+ y 1) pos sols))))
   ; Start the recursion.
   (s-rec sz 1 1 '() '()))

 (define (show-queens n)
   (display (list "The" n "queens problem has"
                  (length (solve n))
                  "solutions."))
   (newline))

 (show-queens 4))))

;regular-trace
;6
(run (inject '(begin (define (fib n)
                       (can-start-loop 'label "fib")
                       (if (< n 2)
                           n
                           (+ (fib (- n 1)) (fib (- n 2)))))
                     (fib 10))))

;meta-trace
;7
(define (fib n)
  (if (< n 2)
      n
      (+ (fib (- n 1)) (fib (- n 2)))))

;8
;regular-trace/meta-trace

;
; Towers of Hanoi (source: http://www.cems.uvm.edu/~rsnapp/teaching/cs32/src/hanoi.rkt)
;

(begin

(define (make-list n value)
    (if (zero? n) 
        '()
        (cons value (make-list (- n 1) value))))

(define (remove-all s lst) 
    (cond ((null? lst) '()); an empty list
          ((eq? s (car lst)) (remove-all s (cdr lst)))
          (else (cons (car lst) (remove-all s (cdr lst))))))

(define (initial-state n)
    (make-list n 1))

(define (move-check? src-peg dst-peg state)
    (cond ((null? state) #f) ; There is no disk on peg (first m)!
          ((eq? (car state) src-peg) #t)
          ((eq? (car state) dst-peg) #f)
          (else (move-check? src-peg dst-peg (cdr state)))))

(define (move-disk src-peg dst-peg state)
    (cond ((null? state) '())
          ((eq? (car state) dst-peg) state) ; Move is illegal!
          ((eq? (car state) src-peg) (cons dst-peg (cdr state))) ; Move is legal.
          (else (cons (car state) (move-disk src-peg dst-peg (cdr state))))))

(define (sequential-move move-list state)
    (if (null? move-list) ; Is the move-list empty?
        state
        (let* ((next-move (car move-list))
               (src-peg (car next-move))
               (dst-peg (cadr next-move))
               (next-state (move-disk src-peg dst-peg state)))
          (if (move-check? src-peg dst-peg state)
              (begin
                (printf "Moving smallest disk from peg ~s onto peg ~s in state ~s yields state ~s.\n" 
                        src-peg dst-peg state next-state)
                (sequential-move (cdr move-list) next-state))
              (error 'sequential-move "Illegal move.")
              ))))

(define (agent home-peg target-peg n)
  (let ((spare-peg (car (remove-all home-peg (remove-all target-peg '(1 2 3))))))
    (if (<= n 0)
        '() ; an empty list
        (append (agent home-peg spare-peg (- n 1))
                (list (list home-peg target-peg))
                (agent spare-peg target-peg (- n 1))))))

(define (hanoi n)
  (let ((state (initial-state n)))
    (printf "Initial state: ~s.\n" state)
    (sequential-move (agent 1 3 n) state)))

(hanoi 5))

;9
;regular-trace/meta-trace

(define (bubble-sort vector <<?)  
   (define (bubble-swap vector idx1 idx2)
     (let ((keep (vector-ref vector idx1)))
       (vector-set! vector idx1 (vector-ref vector idx2))
       (vector-set! vector idx2 keep)
       #t))
   (let outer-loop
     ((unsorted-idx (- (vector-length vector) 2)))
     (if (>= unsorted-idx 0)
       (if (let inner-loop
             ((inner-idx 0)
              (has-changed? #f))
             (if (> inner-idx unsorted-idx)
               has-changed?
               (inner-loop (+ inner-idx 1)
                           (if (<<? (vector-ref vector (+ inner-idx 1))
                                    (vector-ref vector inner-idx))
                             (bubble-swap vector inner-idx (+ inner-idx 1))
                             has-changed?))))
         (outer-loop (- unsorted-idx 1))))))

|#