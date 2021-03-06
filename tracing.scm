(module tracing racket
  
  (provide ;; Trace-key
   (struct-out trace-key)
   make-guard-trace-key
   make-label-trace-key
   make-mp-trace-key
   
   ;; Trace-node
   (struct-out trace-node)
   add-execution!
   trace-node-copy
   
   ;; Tracer-context
   (struct-out tracer-context)
   new-tracer-context
   tracer-context-copy
   
   ;; Start tracing
   start-tracing-guard
   start-tracing-label
   start-tracing-mp
   
   ;;Stop tracing
   stop-tracing
   
   ;; Finding traces
   get-trace
   trace-exists?
   
   ;; Recording trace
   append-trace
   clear-trace
   is-tracing-label?
   
   ;; Loop hotness
   get-times-label-encountered
   inc-times-label-encountered
   
   ;; Trace merging
   inc-splits-cf-id!
   pop-splits-cf-tc
   push-splits-cf-tc
   top-splits-cf-tc)
  
  (require "dictionary.scm"
           "interaction.scm"
           "stack.scm"
           "trace-outputting.scm")
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                        Tracing bookkeeping                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Trace keys
  ;
  
  (struct trace-key (label debug-info) #:transparent)
  (struct guard-trace-key trace-key (guard-id))
  (struct label-trace-key trace-key ())
  (struct mp-trace-key trace-key (mp-id))
  
  (define (make-guard-trace-key label debug-info guard-id)
    (guard-trace-key label debug-info guard-id))
  
  (define (make-label-trace-key label debug-info)
    (label-trace-key label debug-info))
  
  (define (make-mp-trace-key label debug-info mp-id)
    (mp-trace-key label debug-info mp-id))
  
  (define (trace-keys-equal? trace-key-1 trace-key-2)
    (or (and (label-trace-key? trace-key-1) (label-trace-key? trace-key-2)
             (equal? (trace-key-label trace-key-1) (trace-key-label trace-key-2)))
        (and (guard-trace-key? trace-key-1) (guard-trace-key? trace-key-2)
             (equal? (trace-key-label trace-key-1) (trace-key-label trace-key-2))
             (equal? (guard-trace-key-guard-id trace-key-1) (guard-trace-key-guard-id trace-key-2)))
        (and (mp-trace-key? trace-key-1) (mp-trace-key? trace-key-2)
             (equal? (trace-key-label trace-key-1) (trace-key-label trace-key-2))
             (equal? (mp-trace-key-mp-id trace-key-1) (mp-trace-key-mp-id trace-key-2)))))
  
  ;
  ; Trace nodes
  ;
  
  (struct trace-node (trace-key
                      trace
                      (executions #:mutable)) )
  
  (define (make-trace-node trace-key trace)
    (trace-node trace-key trace '()))
  
  ;;; Used for benchmarking purposes
  (define (add-execution! trace-node)
    (let ((old-executions (trace-node-executions trace-node))
          (time (current-seconds)))
      (set-trace-node-executions! trace-node (cons time old-executions))))
  
  (define-syntax trace-node-copy
    (syntax-rules ()
      ((_ a-trace-node ...)
       (struct-copy trace-node a-trace-node ...))))
  
  ;
  ; Tracer context
  ;
  
  (struct tracer-context (trace-key
                          label-counters
                          trace-nodes
                          splits-cf-stack
                          τ) #:transparent)
  
  (define (new-tracer-context)
    (tracer-context #f
                    '()
                    '()
                    '()
                    '()))
  
  (define-syntax tracer-context-copy
    (syntax-rules ()
      ((_ a-tracer-context ...)
       (struct-copy tracer-context a-tracer-context ...))))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-guard tracer-context label debug-info guard-id)
    (let ((temp-tracer-context
           (tracer-context-copy tracer-context
                                (trace-key (make-guard-trace-key label debug-info guard-id)))))
      (clear-trace temp-tracer-context)))
  
  (define (start-tracing-label tracer-context label debug-info)
    (let ((temp-tracer-context
           (tracer-context-copy tracer-context
                                (trace-key (make-label-trace-key label debug-info)))))
      (clear-trace temp-tracer-context)))
  
  (define (start-tracing-mp tracer-context label debug-info mp-id)
    (let ((temp-tracer-context
           (tracer-context-copy tracer-context
                                (trace-key (make-mp-trace-key label debug-info mp-id)))))
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
           (new-tracer-context (add-trace tracer-context trace-key full-trace)))
      (stop-tracing-normal new-tracer-context)))
  
  ;
  ; Finding traces
  ;
  
  (define (return-if-existing trace . errormessage)
    (if trace
        trace
        (apply error errormessage)))
  
  (define (search-trace tracer-context trace-key)
    (define (loop trace-nodes)
      (cond ((null? trace-nodes) #f)
            ((trace-keys-equal? (trace-node-trace-key (car trace-nodes)) trace-key) (car trace-nodes))
            (else (loop (cdr trace-nodes)))))
    (loop (tracer-context-trace-nodes tracer-context)))
  
  (define (get-trace tracer-context trace-key)
    (let ((trace-node-found (search-trace tracer-context trace-key)))
      (return-if-existing trace-node-found "Trace not found!" trace-key)))
  
  (define (not-false? value)
    (if value
        #t
        #f))
  
  (define (trace-exists? tracer-context trace-key)
    (not-false? (search-trace tracer-context trace-key)))
  
  ;
  ; Recording trace
  ;
  
  (define (append-trace tracer-context ms)
    (tracer-context-copy tracer-context
                         (τ (append (tracer-context-τ tracer-context) ms))))
  
  (define (clear-trace tracer-context)
    (tracer-context-copy tracer-context
                         (τ '())))
  
  (define (is-tracing-label? tracer-context label)
    (and (tracer-context-trace-key tracer-context)
         (equal? (trace-key-label (tracer-context-trace-key tracer-context)) label)))
  
  ;
  ; Loop hotness
  ;
  
  (struct label-counter (label counter) #:transparent)
  
  ;;; Retrieves the number of times a label has been encountered.
  ;;; In other words, this function returns the 'hotness' of a label.
  (define (get-times-label-encountered tracer-context label)
    (let* ((label-counters (tracer-context-label-counters tracer-context))
           (result (findf (lambda (label-counter)
                            (eq? (label-counter-label label-counter) label))
                          label-counters)))
      (if result
          (label-counter-counter result)
          ;; Label has not been encountered yet, so counter is 0
          0)))
      
  ;;; Increments the number of times a label has been encountered.
  ;;; In other words, this function increases the 'hotness' of a loop.
  (define (inc-times-label-encountered tracer-context label)
    (let*-values (((old-label-counters) (tracer-context-label-counters tracer-context))
                  ((head tail) (splitf-at old-label-counters
                                          (lambda (label-counter)
                                            (not (eq? (label-counter-label label-counter) label)))))
                  ((label-counter-found) (if (null? tail) #f (car tail))))
      (if label-counter-found
          ;; Remove the old label-counter, create a new label-counter with an incremented count and add it to the list of label-counters
          (let* ((new-label-counter (label-counter (label-counter-label label-counter-found)
                                                   (+ (label-counter-counter label-counter-found) 1)))
                 (new-label-counters (cons new-label-counter (append head (cdr tail))))) ; Add new-label-counter
                                                                                         ; Use (cdr tail) to filter out the old label-counter
            (tracer-context-copy tracer-context
                                 (label-counters new-label-counters)))
          ;; No label-counter tuple exists yet for this label, so create a new one with count 1
          (let* ((new-label-counter (label-counter label 1))
                 (new-label-counters (cons new-label-counter old-label-counters)))
            (tracer-context-copy tracer-context
                                 (label-counters new-label-counters))))))
  
  ;
  ; Trace merging
  ;
  
  (define splits-cf-id 0)
  
  (define (inc-splits-cf-id!)
    (define temp splits-cf-id)
    (set! splits-cf-id (+ splits-cf-id 1))
    temp)
  
  (define (pop-splits-cf-tc tracer-context)
    (let ((old-splits-cf-stack (tracer-context-splits-cf-stack tracer-context)))
      (tracer-context-copy tracer-context
                           (splits-cf-stack (cdr old-splits-cf-stack)))))
  
  (define (push-splits-cf-tc tracer-context mp-id)
    (let ((old-splits-cf-stack (tracer-context-splits-cf-stack tracer-context)))
      (tracer-context-copy tracer-context
                           (splits-cf-stack (cons mp-id old-splits-cf-stack)))))
  
  (define (top-splits-cf-tc tracer-context)
    (car (tracer-context-splits-cf-stack tracer-context)))
  
  ;
  ; Adding traces
  ;
  
  (define (write-trace trace-key trace)
    (let ((label (trace-key-label trace-key))
          (debug-info (trace-key-debug-info trace-key)))
      (cond ((label-trace-key? trace-key) (write-label-trace label (gensym) trace debug-info))
            ((guard-trace-key? trace-key) (write-guard-trace (guard-trace-key-guard-id trace-key) trace))
            ((mp-trace-key? trace-key) (write-mp-tail-trace (mp-trace-key-mp-id trace-key) trace))
            (else (error "Trace-key not recognized:" trace-key)))))
  
  (define (add-trace tracer-context trace-key transformed-trace)
    (let* ((label (trace-key-label trace-key))
           (debug-info (trace-key-debug-info trace-key))
           (trace-node (make-trace-node trace-key transformed-trace))
           (trace-nodes-list (tracer-context-trace-nodes tracer-context)))
      (write-trace trace-key transformed-trace)
      (tracer-context-copy tracer-context
                           (trace-nodes (cons trace-node trace-nodes-list))))))
