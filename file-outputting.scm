(module file-outputting racket
  
  (provide make-full-output-file-name
           append-to-file
           write-to-file)
  
  (require racket/date)
  
  (define (make-full-output-file-name base-file-name base-extension)
    (let ((name-datetime-separator " "))
      (define (make-datetime-file-name-part)
        (let* ((seconds (current-seconds))
               (date (seconds->date seconds #t))
               (colon-replace-string ""))
          (date-display-format 'iso-8601)
          (let ((basic-string (date->string date #t)))
            (string-replace basic-string ":" colon-replace-string))))
      (string-append base-file-name name-datetime-separator (make-datetime-file-name-part) "." base-extension)))
  
  (define (output-to-file path text mode)
    (let* ((output-file (open-output-file path #:exists mode)))
      (display text output-file)
      (close-output-port output-file)))
  
  (define (append-to-file path text)
    (output-to-file path text 'append))
  
  (define (write-to-file path text)
    (output-to-file path text 'replace)))