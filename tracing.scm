(module tracing racket
  
  (provide ;; Trace-key
   (struct-out trace-key)
   make-label-trace-key
   
   ;; Trace-node
   (struct-out trace-node)
   make-label-trace
   add-execution!
   trace-node-copy
   
   ;; Tracer-context
   (struct-out tracer-context)
   new-tracer-context
   tracer-context-copy
   
   ;; Start tracing
   start-tracing-label
   
   ;;Stop tracing
   stop-tracing
   
   ;; Finding traces
   label-trace-exists?
   get-label-trace
   
   ;; Adding traces
   add-label-trace
   
   ;; Recording trace
   append-trace
   clear-trace
   is-tracing-label?)
  
  (require "dictionary.scm"
           "interaction.scm"
           "stack.scm"
           "trace-outputting.scm")
  
  ;
  ; tracer-context-copy
  ;
  
  (define-syntax tracer-context-copy
    (syntax-rules ()
      ((_ a-tracer-context ...)
       (struct-copy tracer-context a-tracer-context ...))))
  
  ;
  ; Trace register
  ;
  
  (define (append-trace tracer-context ms)
    (tracer-context-copy tracer-context
                         (τ (append (tracer-context-τ tracer-context) ms))))
  
  (define (clear-trace tracer-context)
    (tracer-context-copy tracer-context
                         (τ '())))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                        Tracing bookkeeping                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Trace keys
  ;
  
  (struct trace-key (label debug-info) #:transparent)
  
  (define (make-label-trace-key label debug-info)
    (trace-key label debug-info))
  
  ;
  ; Trace nodes
  ;
  
  (struct trace-node (trace-key
                      trace
                      (executions #:mutable)) )
  
  (define (make-label-trace trace-key trace)
    (trace-node trace-key trace '()))
  
  ;;; Used for benchmarking purposes
  (define (add-execution! trace-node)
    (let ((old-executions (trace-node-executions trace-node))
          (time (current-seconds)))
      (set-trace-node-executions! trace-node (cons time old-executions))))
  
  
  ;
  ; trace-node-copy
  ;
  
  (define-syntax trace-node-copy
    (syntax-rules ()
      ((_ a-trace-node ...)
       (struct-copy trace-node a-trace-node ...))))
  
  ;
  ; Tracer context
  ;
  
  (struct tracer-context (trace-key
                          trace-nodes
                          τ) #:transparent)
  
  (define (new-tracer-context)
    (tracer-context #f
                    '()
                    '()))
  
  ;
  ; Tracing label
  ;
  
  (define (is-tracing-label? tracer-context label)
    (and (tracer-context-trace-key tracer-context)
         (equal? (trace-key-label (tracer-context-trace-key tracer-context)) label)))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-label tracer-context label debug-info)
    (let ((temp-tracer-context
           (tracer-context-copy tracer-context
                                (trace-key (make-label-trace-key label debug-info)))))
      (clear-trace temp-tracer-context)))
  
  ;
  ; Stop tracing
  ;
  
  (define (loop-trace-instruction)
    (lambda (program-state)
      (error-return (trace-loops))))
  
  (define (add-loop-trace-instruction trace)
    (append trace (list (loop-trace-instruction))))
  
  (define (stop-tracing-bookkeeping tracer-context)
    (let* ((temp-tracer-context
            (tracer-context-copy  tracer-context
                                  (trace-key #f))))
      (clear-trace temp-tracer-context)))
  
  (define (stop-tracing-normal tracer-context)
    (stop-tracing-bookkeeping tracer-context))
  
  (define (stop-tracing tracer-context looping?)
    (let* ((trace (tracer-context-τ tracer-context))
           (full-trace (if looping?
                           (add-loop-trace-instruction trace)
                           trace))
           (trace-key (tracer-context-trace-key tracer-context))
           (new-tracer-context (add-label-trace tracer-context trace-key full-trace)))
      (stop-tracing-normal new-tracer-context)))
  
  ;
  ; Finding traces
  ;
  
  (define (return-if-existing trace . errormessage)
    (if trace
        trace
        (apply error errormessage)))
  
  (define (search-label-trace tracer-context label)
    (define (loop trace-nodes)
      (cond ((null? trace-nodes) #f)
            ((equal? (trace-key-label (trace-node-trace-key (car trace-nodes))) label) (car trace-nodes)) ;TODO verander equal? naar eq?
            (else (loop (cdr trace-nodes)))))
    (loop (tracer-context-trace-nodes tracer-context)))
  
  (define (get-label-trace tracer-context label)
    (let ((trace-node-found (search-label-trace tracer-context label)))
      (return-if-existing trace-node-found "Label-trace not found!" label)))
  
  ;
  ; Adding traces
  ;
  
  (define (add-label-trace tracer-context trace-key transformed-trace)
    (let* ((label (trace-key-label trace-key))
           (debug-info (trace-key-debug-info trace-key))
           (label-trace (make-label-trace trace-key transformed-trace))
           (trace-nodes-list (tracer-context-trace-nodes tracer-context)))
      (write-label-trace label (gensym) transformed-trace debug-info)
      (tracer-context-copy tracer-context
                           (trace-nodes (cons label-trace trace-nodes-list)))))
  
  ;
  ; Trace exists
  ;
  
  (define (trace-exists? trace)
    (if trace
        #t
        #f))
  
  (define (label-trace-exists? tracer-context label)
    (trace-exists? (search-label-trace tracer-context label))))
