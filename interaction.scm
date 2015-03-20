(module interaction racket
  
  (provide (struct-out ck)
           (struct-out program-state)
           
           (struct-out can-close-loop-encountered)
           (struct-out can-start-loop-encountered)
           (struct-out is-evaluating-encountered))
  
  ;
  ; CK wrappers
  ;
  
  ;;; Represents the state of a program when evaluating an expression.
  ;;; It consists of an expression to be evaluated (e), and a list of continuations to be followed
  ;;; once the evaluation is complete (κ).
  (struct ev (e κ) #:transparent)
  
  ;;; Represents the state of a program when following a continuation.
  ;;; It consists of the continuation to be followed immediately (φ) and a list of continuations
  ;;; to be followed afterwards (κ).
  (struct ko (φ κ) #:transparent)
  
  ;
  ; Program state
  ;
  
  (struct program-state (ck
                         ρ ; env
                         σ ; store
                         θ ; non-kont stack
                         v ; value returned
                         ) #:transparent)
  
  ;
  ; Signaling annotations
  ;
  
  (struct can-close-loop-encountered (label) #:transparent)
  (struct can-start-loop-encountered (label debug-info) #:transparent)
  (struct is-evaluating-encountered (expression) #:transparent)
  
  )
