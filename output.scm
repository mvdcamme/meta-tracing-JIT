(module output racket
  
  (require "constants.scm")
  
  (provide (all-defined-out))
  
  ;
  ; Outputting
  ;
  
  ;;; Prints the given argument to the console, if ENABLE_OUTPUT is set to #t.
  (define (output s)
    (when ENABLE_OUTPUT
      (display s)))
  
  ;;; Prints a newline to the console, if ENABLE_OUTPUT is set to #t.
  (define (output-newline)
    (output #\newline)))