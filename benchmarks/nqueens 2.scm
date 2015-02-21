(begin 

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

 (show-queens 2))