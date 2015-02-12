(module trace-outputting racket
  
  (require (file "file-outputting.scm"))
  
  (provide write-guard-trace
           write-label-trace
           write-mp-tail-trace)
  
  (define BASE_TRACE_OUTPUT_FILE_EXTENSION "scm")
  (define TRACE_OUTPUT_DIRECTORY "./Trace")
  
  (define (add-output-folder file-name)
    (string-append TRACE_OUTPUT_DIRECTORY "/" file-name))
  
  (define (create-trace-output-directory)
    (unless (directory-exists? TRACE_OUTPUT_DIRECTORY)
      (make-directory TRACE_OUTPUT_DIRECTORY)))
  
  (define (write-trace prefix id trace)
    (let* ((base-file-name (add-output-folder (string-append prefix " " (number->string id))))
           (output-file-name (make-full-output-file-name base-file-name BASE_TRACE_OUTPUT_FILE_EXTENSION)))
      (write-to-file output-file-name trace)))
    
  (define (write-guard-trace guard-id trace)
    (write-trace "guard" guard-id trace))
    
  (define (write-label-trace trace-id trace)
    (write-trace "label" trace-id trace))
    
  (define (write-mp-tail-trace mp-id trace)
    (write-trace "mp" mp-id trace))
  
  (create-trace-output-directory))