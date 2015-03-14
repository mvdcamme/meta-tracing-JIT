(module tracing racket
  
  (provide ;; Structs
           (struct-out trace-key)
           (struct-out trace-node)
           (struct-out tracer-context)
           
           (struct-out guard-trace)
           (struct-out label-trace)
           (struct-out mp-tail-trace)
           
           ;; Tracing bookkeeping
           add-ast-node-traced!
           add-execution!
           append-trace!
           call-global-continuation
           clear-trace!
           flush-label-traces-executing!
           get-guard-trace
           get-label-trace
           get-mp-tail-trace
           get-times-label-encountered
           get-label-trace-executing-trace-key
           guard-trace-exists?
           inc-splits-cf-id!
           inc-guard-id!
           inc-times-label-encountered!
           inc-times-label-encountered-while-tracing!
           is-tracing-guard?
           is-tracing-label?
           label-trace-exists?
           make-mp-tail-merges-cf-function
           make-stop-tracing-mp-tail-function
           mp-tail-trace-exists?
           new-tracer-context
           pop-splits-cf-id!
           pop-label-trace-executing!
           push-splits-cf-id!
           push-label-trace-executing!
           push-label-trace-executing-if-not-on-top!
           reset-metrics!
           set-global-continuation!
           set-root-expression-if-uninitialised!
           start-tracing-guard!
           start-tracing-label!
           start-tracing-mp-tail!
           stop-tracing!
           stop-tracing-abnormal!
           stop-tracing-normal!
           times-label-encountered-greater-than-threshold?
           top-splits-cf-id
           top-label-trace-executing
           
           ;; State
           is-executing-trace?
           is-regular-interpreting?
           is-tracing?
           is-tracing-trace-execution?
           set-executing-trace-state!
           set-regular-interpreting-state!
           set-tracing-state!
           set-tracing-trace-execution-state!
           
           ;; Metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
           calculate-trace-duplication
           get-trace-executions
           
           ;; Global variables
           τ
           GLOBAL_CONTINUATION)
  
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
  ; Constants
  ;
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define MAX_TIMES_LABEL_ENCOUNTERED 0)
  (define MAX_TRACE_LENGTH +inf.0)
  
  ;
  ; States
  ;
  
  (define EXECUTING_TRACE_STATE 'executing-trace)
  (define REGULAR_INTERPRETATION_STATE 'regular-interpretation)
  (define TRACING_STATE 'tracing)
  (define TRACING_TRACE_EXECUTION_STATE 'tracing-trace-execution)
  
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
  
  (define (is-tracing-trace-execution? tracer-context)
    (state-equals? tracer-context TRACING_TRACE_EXECUTION_STATE))
  
  (define (set-tracing-trace-execution-state! tracer-context)
    (set-state tracer-context TRACING_TRACE_EXECUTION_STATE))
  
  (define (set-state tracer-context new-state)
    (tracer-context-copy tracer-context (state new-state)))
  
  ;
  ; Trace register
  ;
  
  (define τ #f) ; trace
  
  (define (max-trace-length-reached? tracer-context)
    (> (tracer-context-current-trace-length tracer-context) MAX_TRACE_LENGTH))
  
  (define (handle-max-trace-length-reached tracer-context)
    (display "##### MAX TRACE LENGTH REACHED #####") (newline)
    (set-regular-interpreting-state! (stop-tracing-abnormal! tracer-context)))
  
  (define (append-trace! tracer-context ms)
    (when τ
      (let ((new-instructions-length (length ms)))
        (set! τ (append (reverse ms) τ))
        (add-trace-length! tracer-context new-instructions-length))))
  
  (define (clear-trace! tracer-context)
    (set-tracer-context-current-trace-length! tracer-context 0)
    (set! τ '()))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                        Tracing bookkeeping                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Trace keys
  ;
  
  (define trace-id 0)
  
  (define (new-trace-id!)
    (let ((temp trace-id))
      (set! trace-id (+ trace-id 1))
      temp))
  
  (define (get-parent-label-trace-id trace-key)
    (cond ((guard-trace-key? trace-key) (guard-trace-key-parent-label-trace-id trace-key))
          ((label-trace-key? trace-key) (trace-key-id trace-key))
          ((mp-tail-trace-key? trace-key) (mp-tail-trace-key-parent-label-trace-id trace-key))))
  
  (struct trace-key (label id) #:transparent)
  (struct guard-trace-key trace-key (parent-label-trace-id) #:transparent)
  (struct label-trace-key trace-key (debug-info) #:transparent)
  (struct mp-tail-trace-key trace-key (parent-label-trace-id) #:transparent)
  
  (define (make-guard-trace-key label parent-id)
    (guard-trace-key label (new-trace-id!) parent-id))
  
  (define (make-label-trace-key label debug-info)
    (label-trace-key label (new-trace-id!) debug-info))
  
  (define (make-mp-tail-trace-key label parent-id)
    (mp-tail-trace-key label (new-trace-id!) parent-id))
  
  ;
  ; Trace nodes
  ;
  
  (struct trace-node (trace-key
                      trace
                      (executions #:mutable)))
  
  (define (make-generic-trace-node constructor trace-key trace)
    (constructor trace-key trace '()))
  
  (struct label-trace trace-node ((loops? #:mutable)))
  (struct guard-trace trace-node ())
  (struct mp-tail-trace trace-node ())
  
  (define (make-label-trace trace-key trace loops?)
    (label-trace trace-key trace '() loops?))
  
  (define (make-guard-trace trace-key trace)
    (make-generic-trace-node guard-trace trace-key trace))
  
  (define (make-mp-tail-trace trace-key trace)
    (make-generic-trace-node mp-tail-trace trace-key trace))
  
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
                          times-label-encountered-while-tracing
                          (current-trace-length #:mutable) ;TODO mutable houden voorlopig
                          labels-encountered
                          trace-nodes
                          trace-nodes-dictionary
                          labels-executing
                          splits-cf-id-stack
                          closing-function
                          merges-cf-function
                          guards-dictionary
                          mp-tails-dictionary) #:transparent)
  
  (define (new-tracer-context)
    (tracer-context REGULAR_INTERPRETATION_STATE
                    #f
                    0
                    0
                    '()
                    '()
                    (new-dictionary = 100 (lambda (label-trace-id) label-trace-id))
                    (new-stack)
                    (new-stack)
                    #f
                    #f
                    (new-dictionary equal? 100 (lambda (guard-id) (if (pair? guard-id) (car guard-id) guard-id)))
                    (new-dictionary = 100 (lambda (splits-cf-id) splits-cf-id))))
  
  (define (is-tracing-label? tracer-context label)
    (and (tracer-context-trace-key tracer-context)
         (equal? (trace-key-label (tracer-context-trace-key tracer-context)) label)))
  
  (define (is-tracing-guard? tracer-context)
    (let ((trace-key (tracer-context-trace-key tracer-context)))
      (guard-trace-key? trace-key)))
  
  (define (inc-times-label-encountered-while-tracing! tracer-context)
    (let ((counter (tracer-context-times-label-encountered-while-tracing tracer-context)))
      (tracer-context-copy tracer-context (times-label-encountered-while-tracing (+ counter 1)))))
  
  (define (times-label-encountered-greater-than-threshold? tracer-context)
    (let ((counter (tracer-context-times-label-encountered-while-tracing tracer-context)))
      (> counter MAX_TIMES_LABEL_ENCOUNTERED)))
  
  (define (add-trace-length! tracer-context n)
    (let ((current-length (tracer-context-current-trace-length tracer-context)))
      (set-tracer-context-current-trace-length! tracer-context (+ current-length n))
      (when (max-trace-length-reached? tracer-context)
        (handle-max-trace-length-reached tracer-context))))
  
  ;
  ; Continuation
  ;
  
  (define GLOBAL_CONTINUATION #f)
  
  (define (call-global-continuation value)
    (GLOBAL_CONTINUATION value))
  
  (define (set-global-continuation! k)
    (set! GLOBAL_CONTINUATION k))
  
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
                             (cons (mcons label 1) labels-encountered)))
      (if pair
          (begin (set-mcdr! pair (+ (mcdr pair) 1))
                 tracer-context)
          (add-new-label-encountered))))
  
  ;
  ; Guard counter
  ;
  
  (define guard-id 0)
  
  (define (inc-guard-id!)
    (let ((temp guard-id))
      (set! guard-id (+ guard-id 1))
      temp))
  
  ;
  ; Splits-cf counter
  ;
  
  (define splits-cf-id 0)
  
  (define (inc-splits-cf-id!)
    (let ((temp splits-cf-id))
      (set! splits-cf-id (+ splits-cf-id 1))
      temp))
  
  ;
  ; Pushing/popping cf-ids
  ;
  
  (define (push-splits-cf-id! tracer-context splits-cf-id)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack tracer-context)))
      (push! splits-cf-id-stack splits-cf-id)))
  
  (define (pop-splits-cf-id! tracer-context)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack tracer-context)))
      (pop! splits-cf-id-stack)))
  
  (define (top-splits-cf-id tracer-context)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack tracer-context)))
      (top splits-cf-id-stack)))
  
  ;
  ; Labels executing stack
  ;
  
  (define (flush-label-traces-executing! tracer-context)
    (tracer-context-copy tracer-context (labels-executing (new-stack))))
  
  (define (pop-label-trace-executing! tracer-context)
    (let ((trace-nodes-executing (tracer-context-labels-executing tracer-context)))
      (pop! trace-nodes-executing)))
  
  (define (push-label-trace-executing! tracer-context trace-node)
    (let ((trace-nodes-executing (tracer-context-labels-executing tracer-context)))
      (push! trace-nodes-executing trace-node)))
  
  (define (push-label-trace-executing-if-not-on-top! tracer-context trace-node)
    (unless (and (not (is-empty? (tracer-context-labels-executing tracer-context)))
                 (equal? (trace-key-label (get-label-trace-executing-trace-key tracer-context))
                         (trace-key-label (trace-node-trace-key trace-node))))
      (push-label-trace-executing! tracer-context trace-node)))
  
  (define (top-label-trace-executing tracer-context)
    (let ((trace-nodes-executing (tracer-context-labels-executing tracer-context)))
      (top trace-nodes-executing)))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-guard! tracer-context guard-id old-trace-key)
    (let* ((temp-tracer-context
            (tracer-context-copy tracer-context
                                 (closing-function (make-stop-tracing-guard-function tracer-context guard-id))
                                 (merges-cf-function (make-guard-merges-cf-function tracer-context guard-id))
                                 (trace-key (make-guard-trace-key (trace-key-label old-trace-key)
                                                                  (get-parent-label-trace-id old-trace-key)))
                                 (state TRACING_STATE))))
      (clear-trace! temp-tracer-context)))
  
  (define (start-tracing-label! tracer-context label debug-info)
    (let* ((temp-tracer-context
            (tracer-context-copy tracer-context
                                 (closing-function tracer-context (make-stop-tracing-label-function tracer-context))
                                 (merges-cf-function tracer-context (make-label-merges-cf-function tracer-context))
                                 (state TRACING_STATE)
                                 (trace-key tracer-context (make-label-trace-key label debug-info)))))
      (clear-trace! temp-tracer-context)))
  
  (define (start-tracing-mp-tail! tracer-context mp-id)
    (let* ((temp-tracer-context tracer-context
                                (closing-function tracer-context (make-stop-tracing-mp-tail-function tracer-context mp-id))
                                (merges-cf-function tracer-context (make-mp-tail-merges-cf-function tracer-context mp-id))
                                (state TRACING_STATE)))
      (clear-trace! tracer-context)))

  ;
  ; Stop tracing
  ;
  
  (define (make-stop-tracing-guard-function tracer-context guard-id)
    (define (stop-tracing-guard! trace looping?)
      (let* ((trace-key (tracer-context-trace-key tracer-context))
             (label (trace-key-label trace-key))
             (parent-id (get-parent-label-trace-id trace-key))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-guard-trace-function tracer-context parent-id looping?))))
        (add-guard-trace! tracer-context label parent-id guard-id transformed-trace)))
    stop-tracing-guard!)
  
  (define (make-stop-tracing-label-function tracer-context)
    (define (stop-tracing-label! trace looping?)
      (let* ((trace-key (tracer-context-trace-key tracer-context))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-label-trace-function looping?))))
        (add-label-trace! tracer-context trace-key transformed-trace looping?)))
    stop-tracing-label!)
  
  (define (make-stop-tracing-mp-tail-function tracer-context mp-id)
    (define (stop-tracing-mp-tail! mp-tail looping?)
      (let* ((trace-key (tracer-context-trace-key tracer-context))
             (parent-id (get-parent-label-trace-id trace-key))
             (label (trace-key-label trace-key))
             (transformed-mp-tail (transform-and-optimize-trace mp-tail (make-transform-mp-tail-trace-function tracer-context parent-id looping?))))
        (add-mp-tail-trace! tracer-context mp-id trace-key transformed-mp-tail)))
    stop-tracing-mp-tail!)
  
  (define (stop-tracing-bookkeeping! tracer-context)
    (let* ((temp-tracer-context
            (tracer-context-copy  tracer-context
                                  (trace-key #f)
                                  (closing-function tracer-context #f)
                                  (times-label-encountered-while-tracing tracer-context 0))))
      (clear-trace! temp-tracer-context)))
  
  (define (stop-tracing-abnormal! tracer-context)
    (flush-ast-nodes-traced!)
    (stop-tracing-bookkeeping! tracer-context))
  
  (define (stop-tracing-normal! tracer-context)
    (let ((current-trace-key-id (trace-key-id (tracer-context-trace-key tracer-context))))
      (do-ast-nodes-traced! current-trace-key-id)
      (stop-tracing-bookkeeping! tracer-context)))
  
  (define (stop-tracing! tracer-context looping?)
    (let ((stop-tracing-function (tracer-context-closing-function tracer-context)))
      (stop-tracing-function (reverse τ) looping?)
      (stop-tracing-normal! tracer-context)))
  
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
  
  (define (search-guard-trace tracer-context guard-id)
    (let ((guard-traces-dictionary (tracer-context-guards-dictionary tracer-context)))
      (find guard-traces-dictionary guard-id)))
  
  (define (get-guard-trace tracer-context guard-id)
    (let* ((trace-node-found (search-guard-trace tracer-context guard-id)))
      (return-if-existing trace-node-found "Guard-trace not found!" guard-id)))
  
  (define (search-label-trace tracer-context label)
    (define (loop trace-nodes)
      (cond ((null? trace-nodes) #f)
            ((equal? (trace-key-label (trace-node-trace-key (car trace-nodes))) label) (car trace-nodes)) ;TODO verander equal? naar eq?
            (else (loop (cdr trace-nodes)))))
    (loop (tracer-context-trace-nodes tracer-context)))
  
  (define (get-label-trace tracer-context label)
    (let ((trace-node-found (search-label-trace tracer-context label)))
      (return-if-existing trace-node-found "Label-trace not found!" label)))
  
  (define (search-mp-tail-trace tracer-context mp-id)
    (let ((mp-tail-dictionary (tracer-context-mp-tails-dictionary tracer-context)))
      (find mp-tail-dictionary mp-id)))
  
  (define (get-mp-tail-trace tracer-context mp-id)
    (let ((trace-node-found (search-mp-tail-trace tracer-context mp-id)))
      trace-node-found))
  
  ;
  ; Adding traces
  ;
  
  (define (add-guard-trace! tracer-context label parent-id guard-id trace)
    (let* ((new-guard-trace-key (make-guard-trace-key label parent-id))
           (guard-traces-dictionary (tracer-context-guards-dictionary tracer-context))
           (guard-trace (make-guard-trace new-guard-trace-key trace)))
      (write-guard-trace guard-id trace)
      (insert! guard-traces-dictionary guard-id guard-trace)))
  
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
      (tracer-context-copy tracer-context (trace-nodes (cons label-trace trace-nodes-list)))))
  
  (define (add-mp-tail-trace! tracer-context mp-id trace-key transformed-trace)
    (write-mp-tail-trace mp-id transformed-trace)
    (let ((mp-tail-traces-dictionary (tracer-context-mp-tails-dictionary tracer-context))
          (mp-tail-trace (make-mp-tail-trace trace-key transformed-trace)))
      (insert! mp-tail-traces-dictionary mp-id mp-tail-trace)))
  
  ;
  ; Trace exists
  ;
  
  (define (trace-exists? trace)
    (if trace
        #t
        #f))
  
  (define (guard-trace-exists? tracer-context guard-id)
    (trace-exists? (search-guard-trace tracer-context guard-id)))
  
  (define (label-trace-exists? tracer-context label)
    (trace-exists? (search-label-trace tracer-context label)))
  
  (define (mp-tail-trace-exists? tracer-context mp-id)
    (trace-exists? (search-mp-tail-trace tracer-context mp-id)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                              Metrics                                                 ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Auxiliary functions
  ;
  
  (define (map-over-trace-tree tracer-context f)
    (define (2-ary-f id trace-node)
      (f trace-node))
    (for-each f (tracer-context-trace-nodes tracer-context))
    (table-for-each 2-ary-f (tracer-context-guards-dictionary tracer-context)))
  
  ;
  ; Total nr of traces
  ;
  
  (define (calculate-total-number-of-traces tracer-context)
    (let ((sum 0))
      (define (inc-sum!)
        (set! sum (+ sum 1)))
      (map-over-trace-tree tracer-context (lambda (ignored) (inc-sum!)))
      sum))
  
  ;
  ; Total trace length
  ;
  
  (define (calculate-total-traces-length tracer-context)
    (let ((sum 0))
      (define (add-trace-length! trace-node)
        (set! sum (+ sum (length (get-instruction-list (trace-node-trace trace-node))))))
      (define (get-instruction-list s-expression)
        (cddadr (caadr s-expression)))
      (map-over-trace-tree tracer-context add-trace-length!)
      (table-for-each (lambda (ignored mp-tail-trace-node)
                        (add-trace-length! mp-tail-trace-node))
                      (tracer-context-mp-tails-dictionary tracer-context))
      sum))
  
  ;
  ; Average trace length
  ;
  
  (define (calculate-average-trace-length tracer-context)
    (let ((total-number-of-traces (calculate-total-number-of-traces tracer-context)))
      (if (= total-number-of-traces 0)
          "No traces were formed"
          (/ (calculate-total-traces-length tracer-context) total-number-of-traces))))
  
  ;
  ; Trace duplication
  ;
  
  (define ast-nodes-traced '())
  
  (define (flush-ast-nodes-traced!)
    (set! ast-nodes-traced '()))
  
  (define (add-ast-node-traced! ast-node)
    (set! ast-nodes-traced (cons ast-node ast-nodes-traced)))
  
  (define (do-ast-nodes-traced! trace-key-id)
    (for-each (lambda (ast-node)
                (inc-duplication-counter! ast-node trace-key-id))
              ast-nodes-traced)
    (flush-ast-nodes-traced!))
  
  (struct not-initialised ())
  
  (define root-expression (not-initialised))
  
  (define (root-expression-set?)
    (not (not-initialised? root-expression)))
  
  (define (set-root-expression! exp)
    (set! root-expression exp))
  
  (define (set-root-expression-if-uninitialised! exp)
    (unless (root-expression-set?)
      (set-root-expression! exp)))
  
  (define (reset-trace-duplication-metric!)
    (set-root-expression! (not-initialised)))
  
  (define (inc-duplication-counter! exp trace-key-id)
    (let ((existing-ids (vector-ref exp 1)))
      (when (not (member trace-key-id existing-ids))
        (vector-set! exp 1 (cons trace-key-id existing-ids)))))
  
  (define (calculate-trace-duplication)
    (let ((number-of-nodes 0)
          (total-times-traced 0)
          (all-ast-nodes '()))
      (define (rec node)
        (cond ((vector? node) (set! all-ast-nodes (cons node all-ast-nodes))
                              (let ((list-length (length (vector-ref node 1))))
                                (when (> list-length 0)
                                  (set! number-of-nodes (+ number-of-nodes 1))
                                  (set! total-times-traced (+ total-times-traced list-length))))
                              (rec (vector-ref node 0)))
              ((list? node) (map rec node))))
      (rec root-expression)
      (if (= number-of-nodes 0)
          "No traces were formed"
          (list root-expression
                all-ast-nodes
                (/ total-times-traced number-of-nodes)))))
  
  ;
  ; Trace executions
  ;
  
  (define (get-trace-executions tracer-context)
    (let ((label-traces '())
          (guard-traces '())
          (mp-tail-traces '()))
      (define (add-trace-node-execution-info trace-node)
        (let ((binding (cons (trace-key-label (trace-node-trace-key trace-node)) (trace-node-executions trace-node))))
          (cond ((label-trace? trace-node) (set! label-traces (cons binding label-traces)))
                ((guard-trace? trace-node) (set! guard-traces (cons binding guard-traces)))
                ((mp-tail-trace? trace-node) (set! mp-tail-traces (cons binding mp-tail-traces)))
                (else (error "Unrecognized trace-node encountered: " trace-node)))))
      (map-over-trace-tree tracer-context add-trace-node-execution-info)
      (table-for-each (lambda (ignored mp-tail-trace-node)
                        (add-trace-node-execution-info mp-tail-trace-node))
                      (tracer-context-mp-tails-dictionary tracer-context))
      (list label-traces guard-traces mp-tail-traces)))
  
  ;
  ; Resetting metrics
  ;
  
  (define (reset-metrics!)
    (reset-trace-duplication-metric!))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                        Transforming traces                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Optimizing traces
  ;
  
  (define (changes-env? instruction)
    (or (eq? instruction 'guard-false)
        (eq? instruction 'guard-true)
        (eq? instruction 'guard-same-closure)
        (eq? instruction 'alloc-var)
        (eq? instruction 'set-env)
        (eq? instruction 'switch-to-clo-env)))
  
  ;#f = don't copy the instruction into the final trace
  ;#t = do copy the instruction into the final trace
  
  (define (save-last-env-save stack)
    (set-mcdr! (car stack) #t))
  
  (define (save-all-env-saves stack)
    (for-each (lambda (pair)
                (set-mcdr! pair #t))
              stack))
  
  (define (copy-relevant-instructions list)
    (define (loop to-copy copied)
      (cond ((null? to-copy) (reverse copied))
            ((mcdr (car to-copy)) (loop (cdr to-copy) (cons (mcar (car to-copy)) copied)))
            (else (loop (cdr to-copy) copied))))
    (loop list '()))
  
  (define (optimize-trace trace)
    (define (first-run trace stack first-run-through)
      (cond ((null? trace) (save-all-env-saves stack) (reverse first-run-through))
            ((eq? (caar trace) 'save-env)
             (let ((pair (mcons (car trace) #f)))
               (first-run (cdr trace) (cons pair stack) (cons pair first-run-through))))
            ((eq? (caar trace) 'restore-env)
             (cond ((null? stack)
                    (let ((pair (mcons (car trace) #t)))
                      (first-run (cdr trace) stack (cons pair first-run-through))))
                   ((mcdr (car stack))
                    ;; The environment should be saved and restored
                    (let ((pair (mcons (car trace) #t)))
                      (first-run (cdr trace) (cdr stack) (cons pair first-run-through))))
                   (else 
                    (let ((pair (mcons (car trace) #f)))
                      ;; Not really necessary to add the pair to the first-run-through list
                      (first-run (cdr trace) (cdr stack) (cons pair first-run-through))))))
            ((changes-env? (caar trace))
             (let ((pair (mcons (car trace) #t)))
               (unless (null? stack) (save-last-env-save stack))
               (first-run (cdr trace) stack (cons pair first-run-through))))
            (else
             (let ((pair (mcons (car trace) #t)))
               (first-run (cdr trace) stack (cons pair first-run-through))))))
    (define first-run-through (first-run trace '() '()))
    (copy-relevant-instructions first-run-through))
  
  ;
  ; Transforming traces
  ;
  
  (define (transform-trace-non-looping-plain trace)
    `(letrec ((non-loop ,(append '(lambda ()) trace)))
       (non-loop)))
  
  (define (transform-trace-non-looping trace)
    `(letrec ((non-loop ,(append '(lambda ()) trace)))
       (non-loop)
       (let ((new-state (ko (car τ-κ) (cdr τ-κ))))
         (pop-continuation)
         new-state)))
  
  (define (make-transform-guard-trace-looping tracer-context label-trace-id)
    (define (transform-guard-trace-looping trace)
      `(letrec ((non-loop ,(append '(lambda ()) trace)))
         (non-loop)
         (execute-label-trace-with-id ,tracer-context ,label-trace-id)))
    transform-guard-trace-looping)
  
  (define (transform-label-trace-looping trace)
    `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
       (loop)))
  
  (define (make-transform-guard-trace-function tracer-context label-trace-id looping?)
    (if looping?
        (make-transform-guard-trace-looping tracer-context label-trace-id)
        transform-trace-non-looping))
  
  (define (make-transform-label-trace-function looping?)
    (if looping?
        transform-label-trace-looping
        transform-trace-non-looping))
  
  (define (make-transform-mp-tail-trace-function tracer-context label-trace-id looping?)
    (if looping?
        (make-transform-guard-trace-looping tracer-context label-trace-id)
        transform-trace-non-looping))
  
  (define (transform-trace trace loop-closed?)
    (if loop-closed?
        `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
           (loop))
        `(letrec ((non-loop ,(append '(lambda ()) trace)))
           (non-loop))))
  
  (define (transform-and-optimize-trace trace transformation-function)
    (if ENABLE_OPTIMIZATIONS
        (transformation-function (optimize-trace trace))
        (transformation-function trace)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                      Trace merging                                                   ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Merging traces
  ;
  
  (define (transform-merging-trace trace)
    ;; Since the final instruction in the trace (should) consists of a call to some mp-tail-trace,
    ;; we can use the transform-trace-non-looping-plain function, because it doesn't make sense
    ;; to return the next state of the interpreter at the end of this trace: that should be done
    ;; in the mp-tail-trace to which this trace links.
    (transform-and-optimize-trace trace transform-trace-non-looping-plain))
  
  (define (make-guard-merges-cf-function tracer-context guard-id)
    (define (guard-merges-cf! trace)
      (let* ((trace-key-to-trace (tracer-context-trace-key tracer-context))
             (label (trace-key-label trace-key-to-trace))
             (parent-id (get-parent-label-trace-id trace-key-to-trace))
             (transformed-trace (transform-merging-trace trace))
             (temp-tracer-context (tracer-context-copy  tracer-context
                                                        (closing-function (lambda (trace looping?) '()))
                                                        (trace-key (make-mp-tail-trace-key label parent-id)))))
        (add-guard-trace! temp-tracer-context label parent-id guard-id transformed-trace)))
    guard-merges-cf!)
  
  (define (make-label-merges-cf-function tracer-context)
    (define (label-merges-cf! trace)
      (let ((trace-key (tracer-context-trace-key tracer-context))
            (transformed-trace (transform-merging-trace trace)))
        ;; At the moment a merges-annotation is found, we cannot know whether the label-trace will loop or not.
        ;; TODO register some kind of callback to make sure that, when tracing finishes, the loops? field is updated with the correct value
        (add-label-trace! tracer-context trace-key transformed-trace #f)))
    label-merges-cf!)
  
  (define (make-mp-tail-merges-cf-function tracer-context mp-id)
    (define (mp-tail-merges-cf! trace)
      (let* ((trace-key (tracer-context-trace-key tracer-context))
             (label (trace-key-label trace-key))
             (transformed-trace (transform-merging-trace trace)))
        (add-mp-tail-trace! tracer-context mp-id trace-key transformed-trace)))
    mp-tail-merges-cf!))