(module constants racket
  
  (provide (all-defined-out))
  
  ;;; Determines whether all 'output'-statements effectively print their argument to the console
  ;;; or not.
  (define ENABLE_OUTPUT #f)
  
  ;;; Has the following effects:
  ;;;  - Provided the meta-traced interpreter uses the 'random' function defined on this level
  ;;;    (the tracing interpreter) when calling 'random' in the user-program, the random number
  ;;;    that is generated will be created based on a fixed, hardcoded pseudo-random generator state.
  ;;;    This means that the random numbers that are generated are always the same between program executions.
  (define IS_DEBUGGING #t)
  
  )
