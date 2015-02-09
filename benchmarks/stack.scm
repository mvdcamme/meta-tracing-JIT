(module stack racket
  (provide new-stack push! pop! top)
  
  (struct stack (lst) #:mutable)
  
  (define (new-stack)
    (stack '()))
  
  (define (push! stack el)
    (set-stack-lst! stack (cons el (stack-lst stack))))
  
  (define (pop! stack)
    (let ((lst (stack-lst stack)))
      (if (null? lst)
          (error "Pop!: Stack is empty!")
          (begin (set-stack-lst! stack (cdr lst))
                 (car lst)))))
  
  (define (top stack)
    (let ((lst (stack-lst stack)))
      (if (null? lst)
          (error "Top: Stack is empty!")
          (car lst))))
  
  )