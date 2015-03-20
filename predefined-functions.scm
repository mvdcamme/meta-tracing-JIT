(module predefined-functions racket
  
  (require "closures.scm"
           "constants.scm"
           "environment.scm")
  
  (provide )
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                       Predefined functions                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Programs evaluated by the tracing interpreter do not start out with an empty environment.
  ;;; The environment is initiated with a number of predefined functions.
  
  ;
  ; Random
  ;
  
  (define PSEUDO_RANDOM_GENERATOR_STATE '#(2816165110 2738388292 45348490 3966956132 40780214 47365848))
  
  (define (create-random-generator)
    (vector->pseudo-random-generator PSEUDO_RANDOM_GENERATOR_STATE))
  
  (define PSEUDO_RANDOM_GENERATOR (create-random-generator))
  
  (define meta-random-address 0)
  (define pseudo-random-generator-address 1)
  
  (define pseudo-random (clo (lam '(max)
                                  `((random max pseudo-random-generator)))
                             (env `((pseudo-random-generator . ,pseudo-random-generator-address)))))
  (define regular-random (clo (lam '(max)
                                   '((random max)))
                              (env '())))
  
  (define meta-random (if IS_DEBUGGING
                          pseudo-random
                          regular-random))
  
  (define (reset-random-generator!)
    (set! PSEUDO_RANDOM_GENERATOR (create-random-generator)))
  
  (define (set-pseudo-random-generator! new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR_STATE (pseudo-random-generator->vector new-pseudo-random-generator)))
  
  )