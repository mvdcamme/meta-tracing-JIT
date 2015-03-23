(module tracing racket
  
  (provide ;; Trace-key
           (struct-out trace-key)
           make-label-trace
           
           ;; Trace-node
           (struct-out trace-node)
           make-label-trace
           add-execution!
           
           ;; Tracer-context
           (struct-out tracer-context)
           new-tracer-context
           tracer-context-copy
           
           ;; Times label encountered
           get-times-label-encountered
           inc-times-label-encountered
           
           ;; Start tracing
           start-tracing-label
           
           ;;Stop tracing
           stop-tracing
           
           ;; Finding traces
           label-trace-exists?
           get-label-trace
           
           ;; Adding traces
           add-label-trace
           
           ;; Handling state
           is-executing-trace?
           set-executing-trace-state
           is-regular-interpreting?
           set-regular-interpreting-state
           is-tracing?
           set-tracing-state
           
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
  ; States
  ;
  
  (define EXECUTING_TRACE_STATE 'executing-trace)
  (define REGULAR_INTERPRETATION_STATE 'regular-interpretation)
  (define TRACING_STATE 'tracing)
  
  (define (state-equals? tracer-context state)
    (eq? (tracer-context-state tracer-context) state))
  
  (define (is-executing-trace? tracer-context)
    (state-equals? tracer-context EXECUTING_TRACE_STATE))
  
  (define (set-executing-trace-state tracer-context)
    (set-state tracer-context EXECUTING_TRACE_STATE))
  
  (define (is-regular-interpreting? tracer-context)
    (state-equals? tracer-context REGULAR_INTERPRETATION_STATE))
  
  (define (set-regular-interpreting-state tracer-context)
    (set-state tracer-context REGULAR_INTERPRETATION_STATE))
  
  (define (is-tracing? tracer-context)
    (state-equals? tracer-context TRACING_STATE))
  
  (define (set-tracing-state tracer-context)
    (set-state tracer-context TRACING_STATE))
  
  (define (set-state tracer-context new-state)
    (tracer-context-copy tracer-context (state new-state)))
  
  ;
  ; Trace register
  ;
  
  (define (append-trace tracer-context ms)
    (tracer-context-copy tracer-context
                         (τ (append (tracer-context-τ tracer-context) ms))))
  
  (define (clear-trace tracer-context)
    (tracer-context-copy tracer-context
                         (τ 0)))
  
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
                      (executions #:mutable)))
  
  (define (make-label-trace trace-key trace loops?)
    (trace-node trace-key trace))
  
  ;;; Used for benchmarking purposes
  (define (add-execution! trace-node)
    (let ((old-executions (trace-node-executions trace-node))
          (time (current-seconds)))
      (set-trace-node-executions! trace-node (cons time old-executions))))
  
  ;
  ; Tracer context
  ;
  
  (struct tracer-context (state
                          trace-key
                          labels-encountered
                          trace-nodes
                          τ) #:transparent)
  
  (define (new-tracer-context)
    (tracer-context REGULAR_INTERPRETATION_STATE
                    #f
                    '()
                    '()
                    #f))
  
  ;
  ; Tracing label
  ;
  
  (define (is-tracing-label? tracer-context label)
    (and (tracer-context-trace-key tracer-context)
         (equal? (trace-key-label (tracer-context-trace-key tracer-context)) label)))
  
  ;
  ; Loop hotness
  ;
  
  (define (get-times-label-encountered tracer-context label)
    (let ((pair (assoc label (tracer-context-labels-encountered tracer-context))))
      (if pair
          (cdr pair)
          0)))
  
  (define (inc-times-label-encountered tracer-context label)
    (let* ((labels-encountered (tracer-context-labels-encountered tracer-context))
           (pair (assoc label (tracer-context-labels-encountered tracer-context))))
      (define (find-label-function assoc)
        (equal? (car assoc) label))
      (define (add-new-label-encountered tracer-context label)
        (tracer-context-copy tracer-context 
                             (labels-encountered (cons (cons label 1) labels-encountered))))
      (define (replace-times-label-encountered)
        (let* ((old-counter (cdr (findf find-label-function (tracer-context-labels-encountered tracer-context))))
               (filtered-times-labels-encountered-list (filter find-label-function (tracer-context-labels-encountered tracer-context)))
               (new-times-labels-encountered-list (cons (cons label (+ old-counter 1)) filtered-times-labels-encountered-list)))
          (tracer-context-copy tracer-context
                               (labels-encountered new-times-labels-encountered-list))))
      (if pair
          (replace-times-label-encountered)
          (add-new-label-encountered))))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-label tracer-context label debug-info)
    (let ((temp-tracer-context
           (tracer-context-copy tracer-context
                                (trace-key (make-label-trace-key label debug-info)))))
      (set-tracing-state (clear-trace temp-tracer-context))))
  
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
           (temp-tracer-context (tracer-context-copy tracer-context
                                                     (τ full-trace)))
           ; TODO Actually add the trace...
           (new-tracer-context temp-tracer-context))
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