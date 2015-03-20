(module interaction racket
  
  (provide (struct-out ck)
           (struct-out program-state)
           
           (struct-out can-close-loop-encountered)
           (struct-out can-start-loop-encountered)
           (struct-out is-evaluating-encountered))
  
  ;
  ; Program state
  ;
  
  (struct ck (c ; control
              κ ; continuation stack
              ) #:transparent)
  
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
