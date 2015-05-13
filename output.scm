(module output racket
  
  (require "constants.scm")
  
  (provide output
           outputln
           output-newline)
  
  ;
  ; Outputting
  ;
  
  (define VERBOSITY_LEVEL 'd)
  
  (define LEVELS '(uv v d e))
  
  ;;; Source: http://stackoverflow.com/questions/15871042/how-do-i-find-the-index-of-an-element-in-a-list-in-racket
  (define (index-of lst ele)
    (let loop ((lst lst)
               (idx 0))
      (cond ((empty? lst) #f)
            ((equal? (first lst) ele) idx)
            (else (loop (rest lst) (add1 idx))))))
  
  (define (verbosity-level-higher-than-equals? level-1 level-2)
    (let ((index-1 (index-of LEVELS level-1))
          (index-2 (index-of LEVELS level-2)))
      (and index-1 index-2
           (>= index-1 index-2))))
  
  ;;; Outputs the given argument to the console if the given verbosity-level is higher than or equals VERBOSITY_LEVEL.
  (define (output-with-verbosity s vl)
    (when (verbosity-level-higher-than-equals? vl VERBOSITY_LEVEL)
      (display s)))
  
  ;;; Prints the given argument to the console, if ENABLE_OUTPUT is set to #t and
  ;;; if the given verbosity-level is higher than or equals VERBOSITY_LEVEL.
  (define (output s (vl 'v))
    (when ENABLE_OUTPUT
      (output-with-verbosity s vl)))
  
  ;;; Prints the given argument followed by a newline to the console, if ENABLE_OUTPUT is set to #t and
  ;;; if the given verbosity-level is higher than or equals VERBOSITY_LEVEL.
  (define (outputln s (vl 'v))
    (output s vl)
    (output-newline vl))
  
  ;;; Prints a newline to the console, if ENABLE_OUTPUT is set to #t and
  ;;; if the given verbosity-level is higher than or equals VERBOSITY_LEVEL.
  (define (output-newline (vl 'v))
    (output #\newline vl)))