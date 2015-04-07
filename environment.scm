(module environment racket
  
  (require "closures.scm"
           "constants.scm")
  
  (provide (all-defined-out))
  
  ;
  ; Environment
  ;
  
  ;;; Represents the environment used by the tracing interpreter.
  (struct env (lst) #:transparent)
  
  ;;; Creates a new environment 
  ;(define (make-new-env)
  ;  (env `((random . ,meta-random-address)))) TODO origineel
  
  ;;; Creates a new environment 
  (define (make-new-env)
    (env '()))
  
  (define (add-var-to-env old-env var adr)
    (let ((old-lst (env-lst old-env)))
      (env (cons (cons var adr) old-lst))))
  
  (define (contains-env? lst)
    (cond ((null? lst) #f)
          ((env? (car lst)) #t)
          (else (contains-env? (cdr lst))))))