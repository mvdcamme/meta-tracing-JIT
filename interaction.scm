(module interaction racket
  
  (provide (all-defined-out))
  
  ;
  ; CK wrappers
  ;
  
  ;;; Represents the control of a program when evaluating an expression e.
  (struct ev (e) #:transparent)
  
  ;;; Represents the control of a program when following a continuation φ.
  (struct ko (φ) #:transparent)
  
  ;
  ; Program state
  ;
  
  ;;; The continuation stack is needed to switch back from trace execution
  ;;; to regular program interpretation.
  
  (struct program-state (c
                         ρ   ; env
                         σ   ; store
                         θ   ; non-kont stack
                         v   ; value returned
                         κ   ;continuation stack
                         ) #:transparent)
  
  (define-syntax program-state-copy
    (syntax-rules ()
      ((_ a-program-state ...)
       (struct-copy program-state a-program-state ...))))
  
  ;
  ; Signaling annotations
  ;
  
  (struct can-close-loop-encountered (label) #:transparent)
  (struct can-start-loop-encountered (label debug-info) #:transparent)
  (struct is-evaluating-encountered (expression) #:transparent)
  
  ;
  ; Return types
  ;
  
  (struct error-return (signal) #:transparent)
  (struct normal-return (program-state) #:transparent)
  
  ;
  ; Cesk return
  ;
  
  (struct cesk-normal-return (program-state
                              trace
                              annotation-signal) #:transparent)
  (struct cesk-abnormal-return (signal) #:transparent)
  
  ;
  ; Cesk signalling
  ;
  
  (struct cesk-stopped ())
  (struct trace (instructions) #:transparent)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Error return signals                                         ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Signaling guard failure
  ;
  
  (struct guard-failed-with-ev (guard-id e) #:transparent)
  (struct guard-failed-with-ko (guard-id φ) #:transparent)
  
  ;
  ; Signaling loops
  ;
  
  (struct trace-loops ())
  
  )
