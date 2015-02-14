(module file-outputting racket
  
  (provide make-full-output-directory-name 
           make-full-output-file-name
           append-to-file
           write-to-file)
  
  (require racket/date)
  
  (define (get-datetime-string)
    (let ((milliseconds (modulo (current-milliseconds) 1000)))
      (define (milliseconds->string ms)
        (cond ((< ms 10) (string-append "00" (number->string ms)))
              ((< ms 100) (string-append "0" (number->string ms)))
              (else (number->string ms))))
      (define (make-datetime-file-name-part)
        (let* ((seconds (current-seconds))
               (date (seconds->date seconds #t))
               (colon-replace-string ""))
          (date-display-format 'iso-8601)
          (let ((basic-string (date->string date #t)))
            (string-append (string-replace basic-string ":" colon-replace-string) "-" (milliseconds->string milliseconds)))))
      (make-datetime-file-name-part)))
  
  (define (make-full-output-directory-name base-directory-name)
    (let ((name-datetime-separator " "))
      (string-append base-directory-name name-datetime-separator (get-datetime-string) "/")))
  
  (define (make-full-output-file-name base-file-name base-extension)
    (let ((name-datetime-separator " "))
      (string-append base-file-name name-datetime-separator (get-datetime-string) "." base-extension)))
  
  (define (output-element element port)
    (if (or (eq? element #\newline)
            (string? element))
        (display element port)
        (pretty-print element port)))
  
  (define (output-to-file path text mode)
    (let* ((output-file (open-output-file path #:exists mode)))
      (output-element text output-file)
      (close-output-port output-file)))
  
  (define (append-to-file path text)
    (output-to-file path text 'append))
  
  (define (write-to-file path text)
    (output-to-file path text 'replace)))