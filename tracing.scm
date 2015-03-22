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
           is-executing-trace?
           is-tracing?
           is-tracing-guard?
           is-tracing-label?
           label-trace-exists?
           make-mp-tail-merges-cf-function
           make-stop-tracing-mp-tail-function
           mp-tail-trace-exists?
           pop-splits-cf-id!
           pop-label-trace-executing!
           push-splits-cf-id!
           push-label-trace-executing!
           push-label-trace-executing-if-not-on-top!
           reset-global-tracer-context!
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
           
           ;; Metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
           calculate-trace-duplication
           get-trace-executions
           
           ;; Global variables
           τ
           GLOBAL_CONTINUATION
           GLOBAL_TRACER_CONTEXT)
  
  (require "dictionary.scm")
  (require "stack.scm")
  (require "trace-outputting.scm")
  
  
  ;
  ; Constants
  ;
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define MAX_TIMES_LABEL_ENCOUNTERED 5)
  (define MAX_TRACE_LENGTH 100000)
  
  ;
  ; Trace register
  ;
  
  (define τ #f) ; trace
  
  (define (max-trace-length-reached?)
    (> (tracer-context-current-trace-length GLOBAL_TRACER_CONTEXT) MAX_TRACE_LENGTH))
  
  (define (handle-max-trace-length-reached)
    (display "##### MAX TRACE LENGTH REACHED #####") (newline)
    (stop-tracing-abnormal!))
  
  (define (append-trace! ms)
    (when τ
      (let ((new-instructions-length (length ms)))
        (set! τ (append (reverse ms) τ))
        (add-trace-length! new-instructions-length)
        (when (max-trace-length-reached?)
          (handle-max-trace-length-reached)))))
  
  (define (clear-trace!)
    (set-tracer-context-current-trace-length! GLOBAL_TRACER_CONTEXT 0)
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
  
  (struct tracer-context (is-tracing?
                          trace-key
                          times-label-encountered-while-tracing
                          current-trace-length
                          labels-encountered
                          trace-nodes
                          trace-nodes-dictionary
                          labels-executing
                          splits-cf-id-stack
                          closing-function
                          merges-cf-function
                          guards-dictionary
                          mp-tails-dictionary) #:transparent #:mutable)
  
  (define GLOBAL_TRACER_CONTEXT #f)
  
  (define (new-tracer-context)
    (tracer-context #f
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
  
  (define (reset-global-tracer-context!)
    (set! GLOBAL_TRACER_CONTEXT (new-tracer-context)))
  
  (define (is-tracing?)
    (tracer-context-is-tracing? GLOBAL_TRACER_CONTEXT))
  
  (define (is-tracing-label? label)
    (and (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)
         (equal? (trace-key-label (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)) label)))
  
  (define (is-tracing-guard?)
    (let ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)))
      (guard-trace-key? trace-key)))
  
  (define (inc-times-label-encountered-while-tracing!)
    (let ((counter (tracer-context-times-label-encountered-while-tracing GLOBAL_TRACER_CONTEXT)))
      (set-tracer-context-times-label-encountered-while-tracing! GLOBAL_TRACER_CONTEXT (+ counter 1))))
  
  (define (times-label-encountered-greater-than-threshold?)
    (let ((counter (tracer-context-times-label-encountered-while-tracing GLOBAL_TRACER_CONTEXT)))
      (> counter MAX_TIMES_LABEL_ENCOUNTERED)))
  
  (define (add-trace-length! n)
    (let ((current-length (tracer-context-current-trace-length GLOBAL_TRACER_CONTEXT)))
      (set-tracer-context-current-trace-length! GLOBAL_TRACER_CONTEXT (+ current-length n))))
  
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
  
  (define (get-times-label-encountered label)
    (let ((pair (massoc label (tracer-context-labels-encountered GLOBAL_TRACER_CONTEXT))))
      (if pair
          (mcdr pair)
          0)))
  
  (define (inc-times-label-encountered! label)
    (let* ((labels-encountered (tracer-context-labels-encountered GLOBAL_TRACER_CONTEXT))
           (pair (massoc label (tracer-context-labels-encountered GLOBAL_TRACER_CONTEXT))))
      (define (add-new-label-encountered)
        (set-tracer-context-labels-encountered! GLOBAL_TRACER_CONTEXT 
                                                (cons (mcons label 1) labels-encountered)))
      (if pair
          (set-mcdr! pair (+ (mcdr pair) 1))
          (add-new-label-encountered))))
  
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
  
  (define (push-splits-cf-id! splits-cf-id)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT)))
      (push! splits-cf-id-stack splits-cf-id)))
  
  (define (pop-splits-cf-id!)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT)))
      (pop! splits-cf-id-stack)))
  
  (define (top-splits-cf-id)
    (let ((splits-cf-id-stack (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT)))
      (top splits-cf-id-stack)))
  
  ;
  ; Labels executing stack
  ;
  
  (define (flush-label-traces-executing!)
    (set-tracer-context-labels-executing! GLOBAL_TRACER_CONTEXT (new-stack)))
  
  (define (pop-label-trace-executing!)
    (let ((trace-nodes-executing (tracer-context-labels-executing GLOBAL_TRACER_CONTEXT)))
      (pop! trace-nodes-executing)))
  
  (define (push-label-trace-executing! trace-node)
    (let ((trace-nodes-executing (tracer-context-labels-executing GLOBAL_TRACER_CONTEXT)))
      (push! trace-nodes-executing trace-node)))
  
  (define (push-label-trace-executing-if-not-on-top! trace-node)
    (unless (and (is-executing-trace?)
                 (equal? (trace-key-label (get-label-trace-executing-trace-key))
                         (trace-key-label (trace-node-trace-key trace-node))))
      (push-label-trace-executing! trace-node)))
  
  (define (top-label-trace-executing)
    (let ((trace-nodes-executing (tracer-context-labels-executing GLOBAL_TRACER_CONTEXT)))
      (top trace-nodes-executing)))
  
  (define (is-executing-trace?)
    (let ((trace-nodes-executing (tracer-context-labels-executing GLOBAL_TRACER_CONTEXT)))
      (not (is-empty? trace-nodes-executing))))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-guard! guard-id old-trace-key)
    (clear-trace!)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-guard-function guard-id))
    (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-guard-merges-cf-function guard-id))
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #t)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-guard-trace-key (trace-key-label old-trace-key)
                                                                               (get-parent-label-trace-id old-trace-key))))
  
  (define (start-tracing-label! label debug-info)
    (clear-trace!)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-label-function))
    (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-label-merges-cf-function))
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #t)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-label-trace-key label debug-info)))
  
  (define (start-tracing-mp-tail! mp-id)
    (clear-trace!)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-mp-tail-function mp-id))
    (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-mp-tail-merges-cf-function mp-id)))

  ;
  ; Stop tracing
  ;
  
  (define (make-stop-tracing-guard-function guard-id)
    (define (stop-tracing-guard! trace looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key))
             (parent-id (get-parent-label-trace-id trace-key))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-guard-trace-function parent-id looping?))))
        (add-guard-trace! label parent-id guard-id transformed-trace)))
    stop-tracing-guard!)
  
  (define (make-stop-tracing-label-function)
    (define (stop-tracing-label! trace looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-label-trace-function looping?))))
        (add-label-trace! trace-key transformed-trace looping?)))
    stop-tracing-label!)
  
  (define (make-stop-tracing-mp-tail-function mp-id)
    (define (stop-tracing-mp-tail! mp-tail looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (parent-id (get-parent-label-trace-id trace-key))
             (label (trace-key-label trace-key))
             (transformed-mp-tail (transform-and-optimize-trace mp-tail (make-transform-mp-tail-trace-function parent-id looping?))))
        (add-mp-tail-trace! mp-id trace-key transformed-mp-tail)))
    stop-tracing-mp-tail!)
  
  (define (stop-tracing-bookkeeping!)
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #f)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT #f)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT #f)
    (set-tracer-context-times-label-encountered-while-tracing! GLOBAL_TRACER_CONTEXT 0)
    (clear-trace!))
  
  (define (stop-tracing-abnormal!)
    (flush-ast-nodes-traced!)
    (stop-tracing-bookkeeping!))
  
  (define (stop-tracing-normal!)
    (let ((current-trace-key-id (trace-key-id (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))))
      (do-ast-nodes-traced! current-trace-key-id)
      (stop-tracing-bookkeeping!)))
  
  (define (stop-tracing! looping?)
    (let ((stop-tracing-function (tracer-context-closing-function GLOBAL_TRACER_CONTEXT)))
      (stop-tracing-function (reverse τ) looping?)
      (stop-tracing-normal!)))
  
  ;
  ; Finding traces
  ;
  
  (define (get-label-trace-executing-trace-key)
    (let ((top-label-trace (top-label-trace-executing)))
      (trace-node-trace-key top-label-trace)))
  
  (define (return-if-existing trace . errormessage)
    (if trace
        trace
        (apply error errormessage)))
  
  (define (search-guard-trace guard-id)
    (let ((guard-traces-dictionary (tracer-context-guards-dictionary GLOBAL_TRACER_CONTEXT)))
      (find guard-traces-dictionary guard-id)))
  
  (define (get-guard-trace guard-id)
    (let* ((trace-node-found (search-guard-trace guard-id)))
      (return-if-existing trace-node-found "Guard-trace not found!" guard-id)))
  
  (define (search-label-trace label)
    (define (loop trace-nodes)
      (cond ((null? trace-nodes) #f)
            ((equal? (trace-key-label (trace-node-trace-key (car trace-nodes))) label) (car trace-nodes)) ;TODO verander equal? naar eq?
            (else (loop (cdr trace-nodes)))))
    (loop (tracer-context-trace-nodes GLOBAL_TRACER_CONTEXT)))
  
  (define (get-label-trace label)
    (let ((trace-node-found (search-label-trace label)))
      (return-if-existing trace-node-found "Label-trace not found!" label)))
  
  (define (search-mp-tail-trace mp-id)
    (let ((mp-tail-dictionary (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT)))
      (find mp-tail-dictionary mp-id)))
  
  (define (get-mp-tail-trace mp-id)
    (let ((trace-node-found (search-mp-tail-trace mp-id)))
      trace-node-found))
  
  ;
  ; Adding traces
  ;
  
  (define (add-guard-trace! label parent-id guard-id trace)
    (let* ((new-guard-trace-key (make-guard-trace-key label parent-id))
           (guards-dictionary (tracer-context-guards-dictionary GLOBAL_TRACER_CONTEXT))
           (guard-trace (make-guard-trace new-guard-trace-key trace)))
      (write-guard-trace guard-id trace)
      (insert! guards-dictionary guard-id guard-trace)))
  
  (define (add-label-trace! trace-key transformed-trace loops?)
    (let* ((label (trace-key-label trace-key))
           (debug-info (label-trace-key-debug-info trace-key))
           (trace-id (trace-key-id trace-key))
           (label-trace (make-label-trace trace-key transformed-trace loops?)))
      (write-label-trace label trace-id transformed-trace debug-info)
      (insert! (tracer-context-trace-nodes-dictionary GLOBAL_TRACER_CONTEXT)
               trace-id
               label-trace)
      (set-tracer-context-trace-nodes! GLOBAL_TRACER_CONTEXT
                                       (cons label-trace
                                             (tracer-context-trace-nodes GLOBAL_TRACER_CONTEXT)))))
  
  (define (add-mp-tail-trace! mp-id trace-key transformed-trace)
    (write-mp-tail-trace mp-id transformed-trace)
    (let ((mp-tails-dictionary (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
          (mp-tail-trace (make-mp-tail-trace trace-key transformed-trace)))
      (insert! mp-tails-dictionary mp-id mp-tail-trace)))
  
  ;
  ; Trace exists
  ;
  
  (define (trace-exists? trace)
    (if trace
        #t
        #f))
  
  (define (guard-trace-exists? guard-id)
    (trace-exists? (search-guard-trace guard-id)))
  
  (define (label-trace-exists? label)
    (trace-exists? (search-label-trace label)))
  
  (define (mp-tail-trace-exists? mp-id)
    (trace-exists? (search-mp-tail-trace mp-id)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                              Metrics                                                 ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Auxiliary functions
  ;
  
  (define (map-over-trace-tree f)
    (define (2-ary-f id trace-node)
      (f trace-node))
    (for-each f (tracer-context-trace-nodes GLOBAL_TRACER_CONTEXT))
    (table-for-each 2-ary-f (tracer-context-guards-dictionary GLOBAL_TRACER_CONTEXT)))
  
  ;
  ; Total nr of traces
  ;
  
  (define (calculate-total-number-of-traces)
    (let ((sum 0))
      (define (inc-sum!)
        (set! sum (+ sum 1)))
      (map-over-trace-tree (lambda (ignored) (inc-sum!)))
      sum))
  
  ;
  ; Total trace length
  ;
  
  (define (calculate-total-traces-length)
    (let ((sum 0))
      (define (add-trace-length! trace-node)
        (set! sum (+ sum (length (get-instruction-list (trace-node-trace trace-node))))))
      (define (get-instruction-list s-expression)
        (cddadr (caadr s-expression)))
      (map-over-trace-tree add-trace-length!)
      (table-for-each (lambda (ignored mp-tail-trace-node)
                        (add-trace-length! mp-tail-trace-node))
                      (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
      sum))
  
  ;
  ; Average trace length
  ;
  
  (define (calculate-average-trace-length)
    (let ((total-number-of-traces (calculate-total-number-of-traces)))
      (if (= total-number-of-traces 0)
          "No traces were formed"
          (/ (calculate-total-traces-length) total-number-of-traces))))
  
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
  
  (define (get-trace-executions)
    (let ((label-traces '())
          (guard-traces '())
          (mp-tail-traces '()))
      (define (add-trace-node-execution-info trace-node)
        (let ((binding (cons (trace-key-label (trace-node-trace-key trace-node)) (trace-node-executions trace-node))))
          (cond ((label-trace? trace-node) (set! label-traces (cons binding label-traces)))
                ((guard-trace? trace-node) (set! guard-traces (cons binding guard-traces)))
                ((mp-tail-trace? trace-node) (set! mp-tail-traces (cons binding mp-tail-traces)))
                (else (error "Unrecognized trace-node encountered: " trace-node)))))
      (map-over-trace-tree add-trace-node-execution-info)
      (table-for-each (lambda (ignored mp-tail-trace-node)
                        (add-trace-node-execution-info mp-tail-trace-node))
                      (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
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
  
  (define (make-transform-guard-trace-looping label-trace-id)
    (define (transform-guard-trace-looping trace)
      `(letrec ((non-loop ,(append '(lambda ()) trace)))
         (non-loop)
         (execute-label-trace-with-id ,label-trace-id)))
    transform-guard-trace-looping)
  
  (define (transform-label-trace-looping trace)
    `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
       (loop)))
  
  (define (make-transform-guard-trace-function label-trace-id looping?)
    (if looping?
        (make-transform-guard-trace-looping label-trace-id)
        transform-trace-non-looping))
  
  (define (make-transform-label-trace-function looping?)
    (if looping?
        transform-label-trace-looping
        transform-trace-non-looping))
  
  (define (make-transform-mp-tail-trace-function label-trace-id looping?)
    (if looping?
        (make-transform-guard-trace-looping label-trace-id)
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
  
  (define (make-guard-merges-cf-function guard-id)
    (define (guard-merges-cf! trace)
      (let* ((trace-key-to-trace (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key-to-trace))
             (parent-id (get-parent-label-trace-id trace-key-to-trace))
             (transformed-trace (transform-merging-trace trace)))
        (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (lambda (trace looping?) '()))
        (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-mp-tail-trace-key label parent-id))
        (add-guard-trace! label parent-id guard-id transformed-trace)))
    guard-merges-cf!)
  
  (define (make-label-merges-cf-function)
    (define (label-merges-cf! trace)
      (let ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
            (transformed-trace (transform-merging-trace trace)))
        ;; At the moment a merges-annotation is found, we cannot know whether the label-trace will loop or not.
        ;; TODO register some kind of callback to make sure that, when tracing finishes, the loops? field is updated with the correct value
        (add-label-trace! trace-key transformed-trace #f)))
    label-merges-cf!)
  
  (define (make-mp-tail-merges-cf-function mp-id)
    (define (mp-tail-merges-cf! trace)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key))
             (transformed-trace (transform-merging-trace trace)))
        (add-mp-tail-trace! mp-id trace-key transformed-trace)))
    mp-tail-merges-cf!))