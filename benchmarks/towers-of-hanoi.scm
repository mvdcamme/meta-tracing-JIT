(begin

(define (make-list n value)
    (if (zero? n) 
        '()
        (cons value (make-list (- n 1) value))))

(define (remove-all s lst) 
    (if (null? lst)
        '()
        (if (eq? s (begin (display "in remove-all, lst = ") (display lst) (car lst)))
            (remove-all s (cdr lst))
            (cons (car lst) (remove-all s (cdr lst))))))

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
        (begin (define next-move (car move-list))
               (define src-peg (car next-move))
               (define dst-peg (cadr next-move))
               (define next-state (move-disk src-peg dst-peg state))
               (if (move-check? src-peg dst-peg state)
                   (begin (printf "Moving smallest disk from peg ~s onto peg ~s in state ~s yields state ~s.\n" 
                                   src-peg dst-peg state next-state)
                          (sequential-move (cdr move-list) next-state))
                   (error 'sequential-move "Illegal move.")))))

(define (agent home-peg target-peg n)
  (define spare-peg (car (remove-all home-peg (remove-all target-peg '(1 2 3)))))
  (if (<= n 0)
      '() ; an empty list
      (append (agent home-peg spare-peg (- n 1))
              (list (list home-peg target-peg))
              (agent spare-peg target-peg (- n 1)))))

(define (hanoi n)
  (define state (initial-state n))
  (printf "Initial state: ~s.\n" state)
  (sequential-move (agent 1 3 n) state))

(hanoi 5))