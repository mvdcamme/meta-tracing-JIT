(module trace-outputting racket
  
  (require (file "file-outputting.scm"))
  
  (provide write-label-trace)
  
  (define BASE_TRACE_OUTPUT_FILE_EXTENSION "scm")
  (define TRACE_OUTPUT_DIRECTORY "./Trace")
  
  (define (add-output-folder file-name)
    (string-append TRACE_OUTPUT_DIRECTORY "/" file-name))
  
  (define (create-trace-output-directory)
    (unless (directory-exists? TRACE_OUTPUT_DIRECTORY)
      (make-directory TRACE_OUTPUT_DIRECTORY)))
  
  (define (write-label-trace trace-id trace)
    (let* ((base-file-name (add-output-folder (string-append "label " (number->string trace-id))))
           (output-file-name (make-full-output-file-name base-file-name BASE_TRACE_OUTPUT_FILE_EXTENSION)))
      (write-to-file output-file-name trace)))
  
  (create-trace-output-directory))