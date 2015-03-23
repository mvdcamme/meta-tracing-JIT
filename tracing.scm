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
           
           is-tracing-label?
           
           ;; Times label encountered
           get-times-label-encountered
           inc-times-label-encountered!
           
           ;; Start tracing
           start-tracing-label!
           
           ;;Stop tracing
           stop-tracing!
           
           ;; Finding traces
           label-trace-exists?
           get-label-trace
           
           ;; Adding traces
           add-label-trace!
           
           ;; Handling state
           is-executing-trace?
           set-executing-trace-state!
           is-regular-interpreting?
           set-regular-interpreting-state!
           is-tracing?
           set-tracing-state!
           
           ;; Recording trace
           append-trace!
           clear-trace!)
  
  (require "dictionary.scm")
  (require "stack.scm")
  (require "trace-outputting.scm")
  
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
  
  (define (set-executing-trace-state! tracer-context)
    (set-state tracer-context EXECUTING_TRACE_STATE))
  
  (define (is-regular-interpreting? tracer-context)
    (state-equals? tracer-context REGULAR_INTERPRETATION_STATE))
  
  (define (set-regular-interpreting-state! tracer-context)
    (set-state tracer-context REGULAR_INTERPRETATION_STATE))
  
  (define (is-tracing? tracer-context)
    (state-equals? tracer-context TRACING_STATE))
  
  (define (set-tracing-state! tracer-context)
    (set-state tracer-context TRACING_STATE))
  
  (define (set-state tracer-context new-state)
    (tracer-context-copy tracer-context (state new-state)))
  
  ;
  ; Trace register
  ;
  
  (define (append-trace! tracer-context ms)
    (when τ
      (let ((new-instructions-length (length ms)))
        (set! τ (append (reverse ms) τ))
        (add-trace-length! tracer-context new-instructions-length))))
  
  (define (clear-trace! tracer-context)
    (set-tracer-context-current-trace-length! tracer-context 0)
    (set! τ '())
    tracer-context)
  
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
    (label-trace-key label (new-trace-id!) debug-info))
  
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
  
  (define (massoc el lst)
    (cond ((null? lst) #f)
          ((eq? el (mcar (car lst))) (car lst))
          (else (massoc el (cdr lst)))))
  
  (define (get-times-label-encountered tracer-context label)
    (let ((pair (massoc label (tracer-context-labels-encountered tracer-context))))
      (if pair
          (mcdr pair)
          0)))
  
  (define (inc-times-label-encountered! tracer-context label)
    (let* ((labels-encountered (tracer-context-labels-encountered tracer-context))
           (pair (massoc label (tracer-context-labels-encountered tracer-context))))
      (define (add-new-label-encountered)
        (tracer-context-copy tracer-context 
                             (labels-encountered (cons (mcons label 1) labels-encountered))))
      (if pair
          (begin (set-mcdr! pair (+ (mcdr pair) 1))
                 tracer-context)
          (add-new-label-encountered))))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-label! tracer-context label debug-info)
    (let* ((temp-tracer-context
            (tracer-context-copy tracer-context
                                 (closing-function (make-stop-tracing-label-function))
                                 (merges-cf-function (make-label-merges-cf-function))
                                 (state TRACING_STATE)
                                 (trace-key (make-label-trace-key label debug-info)))))
      (clear-trace! temp-tracer-context)))

  ;
  ; Stop tracing
  ;
  
  (define (stop-tracing-bookkeeping! tracer-context)
    (let* ((temp-tracer-context
            (tracer-context-copy  tracer-context
                                  (trace-key #f)
                                  (closing-function #f)
                                  (times-label-encountered-while-tracing 0))))
      (clear-trace! temp-tracer-context)
      temp-tracer-context))
  
  (define (stop-tracing-normal! tracer-context)
    (let ((current-trace-key-id (trace-key-id (tracer-context-trace-key tracer-context))))
      (do-ast-nodes-traced! current-trace-key-id)
      (stop-tracing-bookkeeping! tracer-context)))
  
  (define (stop-tracing! tracer-context looping?)
    (let ((stop-tracing-function (tracer-context-closing-function tracer-context)))
      (stop-tracing-normal! (stop-tracing-function tracer-context (reverse τ) looping?))))
  
  ;
  ; Finding traces
  ;
  
  (define (get-label-trace-executing-trace-key tracer-context)
    (let ((top-label-trace (top-label-trace-executing tracer-context)))
      (trace-node-trace-key top-label-trace)))
  
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
  
  (define (add-label-trace! tracer-context trace-key transformed-trace loops?)
    (let* ((label (trace-key-label trace-key))
           (debug-info (label-trace-key-debug-info trace-key))
           (trace-id (trace-key-id trace-key))
           (label-trace (make-label-trace trace-key transformed-trace loops?))
           (label-traces-dictionary (tracer-context-trace-nodes-dictionary tracer-context))
           (trace-nodes-list (tracer-context-trace-nodes tracer-context)))
      (write-label-trace label trace-id transformed-trace debug-info)
      (insert! label-traces-dictionary
               trace-id
               label-trace)
      (set-tracer-context-trace-nodes! tracer-context (cons label-trace trace-nodes-list))
      tracer-context))
  
  ;
  ; Trace exists
  ;
  
  (define (trace-exists? trace)
    (if trace
        #t
        #f))
  
  (define (label-trace-exists? tracer-context label)
    (trace-exists? (search-label-trace tracer-context label))))