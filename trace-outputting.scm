(module trace-outputting racket
  
  (require (file "file-outputting.scm"))
  
  (provide write-guard-trace
           write-label-trace
           write-mp-tail-trace
           reset-trace-outputting!)
  
  (define BASE_TRACE_OUTPUT_FILE_EXTENSION "scm")
  (define BASE_TRACE_OUTPUT_DIRECTORY_PATH "./Traces/Trace")
  
  (define (make-output-directory-path)
    (make-full-output-directory-name BASE_TRACE_OUTPUT_DIRECTORY_PATH))
  
  (define current-trace-output-directory-created #f)
  (define current-trace-output-directory-path #f)
  
  (define (add-output-directory-path-to-file-name file-name)
    (string-append current-trace-output-directory-path file-name))
  
  (define (create-trace-output-directory)
    (unless (directory-exists? current-trace-output-directory-path)
      (set! current-trace-output-directory-created #t)
      (make-directory current-trace-output-directory-path)))
  
  (define (write-trace prefix id trace)
    (let* ((base-file-name (add-output-directory-path-to-file-name (string-append prefix " " (number->string id))))
           (output-file-name (make-full-output-file-name base-file-name BASE_TRACE_OUTPUT_FILE_EXTENSION)))
      (unless current-trace-output-directory-created
        (create-trace-output-directory))
      (write-to-file output-file-name trace)))
    
  (define (write-guard-trace guard-id trace)
    (write-trace "guard" guard-id trace))
    
  (define (write-label-trace trace-id trace debug-info)
    (write-trace (string-append "label " (if (symbol? debug-info) (symbol->string debug-info) debug-info)) trace-id trace))
    
  (define (write-mp-tail-trace mp-id trace)
    (write-trace "mp" mp-id trace))
  
  (define (reset-trace-outputting!)
    (set! current-trace-output-directory-created #f)
    (set! current-trace-output-directory-path (make-output-directory-path)))
  
  (reset-trace-outputting!))