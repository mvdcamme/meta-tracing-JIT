(module interaction racket
  
  (provide (struct-out ck)
           (struct-out program-state)
           (struct-out can-start-loop-encountered)
           (struct-out can-close-loop-encountered))
  
  (struct ck (c ; control
              κ ; continuation stack
              ) #:transparent)
  
  (struct program-state (ck
                         ρ ; env
                         σ ; store
                         θ ; non-kont stack
                         v ; value returned
                         ) #:transparent)
  
  (struct can-start-loop-encountered (label debug-info) #:transparent)
  (struct can-close-loop-encountered (label) #:transparent)
  
  )
