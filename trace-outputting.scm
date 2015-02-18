(module trace-outputting racket
  
  (require (file "file-outputting.scm"))
  
  (provide write-guard-trace
           write-label-trace
           write-mp-tail-trace
           reset-trace-outputting!)
  
  (define TRACES_ROOT_FOLDER "./Traces/")
  
  (define BASE_TRACE_OUTPUT_FILE_EXTENSION "scm")
  (define BASE_TRACE_OUTPUT_DIRECTORY_PATH (string-append TRACES_ROOT_FOLDER "Trace"))
  
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
    (let* ((base-file-name (add-output-directory-path-to-file-name (string-append prefix " " id)))
           (output-file-name (string-append base-file-name "." BASE_TRACE_OUTPUT_FILE_EXTENSION)))
      (unless current-trace-output-directory-created
        (create-trace-output-directory))
      (thread (lambda ()
                (write-to-file output-file-name (transform-trace trace))))))
    
  (define (write-guard-trace guard-id trace)
    (define (transform-guard-id guard-id)
      (cond ((number? guard-id) (number->string guard-id))
            ((pair? guard-id) (string-append (transform-guard-id (car guard-id)) "." (transform-guard-id (cdr guard-id))))))
    (write-trace "guard" (transform-guard-id guard-id) trace))
    
  (define (write-label-trace trace-label trace-id trace debug-info)
    (write-trace (string-append "label " (if (symbol? debug-info) (symbol->string debug-info) debug-info)) (number->string trace-id) trace))
    
  (define (write-mp-tail-trace mp-id trace)
    (write-trace "mp" (number->string mp-id) trace))
  
  (define (reset-trace-outputting!)
    (create-root-traces-folder-if-needed)
    (set! current-trace-output-directory-created #f)
    (set! current-trace-output-directory-path (make-output-directory-path)))
  
  (define (transform-trace trace)
    (define (tree-rec element)
      (cond ((procedure? element) (let ((proc-name (object-name element)))
                                    (if proc-name
                                        (string-append "<procedure:" (symbol->string proc-name) ">")
                                        "<procedure>")))
            ((pair? element) (cons (tree-rec (car element)) (tree-rec (cdr element))))
            ((vector? element) (vector-map tree-rec element))
            (else element)))
    (tree-rec trace))
  
  (define (create-root-traces-folder-if-needed)
    (unless (directory-exists? TRACES_ROOT_FOLDER)
      (make-directory TRACES_ROOT_FOLDER)))
  
  (reset-trace-outputting!))