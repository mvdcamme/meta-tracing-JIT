(module tracing-interpreter racket
  (provide ;; Starting evaluator   
           inject
           run
           
           ;; Structs
           ev
           ko
           
           ;; Registers
           τ-κ
           
           ;; Trace instructions
           add-continuation
           alloc-var
           apply-native
           call-label-trace!
           create-closure
           debug
           execute-guard-trace
           execute-label-trace
           execute-mp-tail-trace
           guard-false
           guard-true
           guard-same-closure
           guard-same-nr-of-args
           literal-value
           lookup-var
           quote-value
           pop-continuation!
           pop-splits-cf-id!
           pop-trace-node-executing!
           pop-trace-node-frame-from-stack!
           pop-trace-frame!
           pop-trace-frame-until-label!
           push-splits-cf-id!
           push-continuation!
           push-trace-node-executing!
           push-trace-frame!
           remove-continuation
           restore-env
           restore-val
           restore-vals
           save-env
           save-all-vals
           save-val
           save-vals
           set-env
           set-var
           switch-to-clo-env
           top-continuation
           top-splits-cf-id
           trace-node-frame-on-stack?
           
           ;; Metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
           calculate-trace-duplication
           get-trace-executions
           
           
           ;; Purely for benchmarking the implementation
           GLOBAL_TRACER_CONTEXT
           set-pseudo-random-generator!)
  
  (require racket/date)
  
  (require "dictionary.scm")
  (require "stack.scm")
  (require "trace-outputting.scm")
  
  (define (member-equal el lst)
    (cond ((null? lst) #f)
          ((equal? el (car lst)) lst)
          (else (member-equal el (cdr lst)))))
  
  ;
  ; Constants
  ;
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define ENABLE_OUTPUT #f)
  (define IS_DEBUGGING #t)
  (define TRACING_THRESHOLD 5)
  (define MAX_TRACE_LENGTH +inf.0)
  
  (define ns (make-base-namespace))
  
  ;
  ; Outputting
  ;
  
  (define (output s)
    (when ENABLE_OUTPUT
      (display s)))
  
  (define (output-newline)
    (output #\newline))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                             CK machine                                               ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; CK wrappers
  ;
  
  (struct ev (e κ) #:transparent)
  (struct ko (φ κ) #:transparent)
  
  ;
  ; Registers
  ;
  
  (define ρ #f) ; env
  (define σ #f) ; store
  (define θ #f) ; non-kont stack
  (define v #f) ; value
  (define τ #f) ; trace
  
  (define τ-κ #f) ;continuation stack
  
  ;
  ; Continuations
  ;
  
  (struct andk (es) #:transparent)
  (struct apply-failedk (rator i) #:transparent)
  (struct applicationk (debug) #:transparent)
  (struct applyk (rator) #:transparent)
  (struct closure-guard-failedk (i) #:transparent)
  (struct condk (pes es) #:transparent)
  (struct definevk (x) #:transparent) ;define variable
  (struct haltk () #:transparent)
  (struct ifk (e1 e2) #:transparent)
  (struct letk (x es) #:transparent)
  (struct let*k (x bds es) #:transparent)
  (struct letreck (x bds es) #:transparent)
  (struct ork (es) #:transparent)
  (struct randk (e es i) #:transparent)
  (struct ratork (i debug) #:transparent)
  (struct seqk (es) #:transparent)
  (struct setk (x) #:transparent)
  
  
  (define gencounter 2)
  (define (new-gencounter!)
    (let ((temp gencounter))
      (set! gencounter (+ gencounter 1))
      temp))
  
  (define (new-store)
    (let ((dict (new-dictionary = 100 (lambda (splits-cf-id) splits-cf-id))))
      (insert! dict meta-random-address meta-random)
      (insert! dict pseudo-random-generator-address PSEUDO_RANDOM_GENERATOR)
      dict))
  
  ;
  ; Tracing annotations continuations
  ;
  
  (struct can-close-loopk () #:transparent)
  (struct can-start-loopk (label debug-info) #:transparent)
  (struct is-evaluatingk () #:transparent)
  
  ;
  ; Closures
  ;
  
  (struct clo (λ ρ) #:transparent)
  (struct lam (x es) #:transparent)
  
  (define (clo-equal? clo1 clo2)
    (or (eq? clo1 clo2)
        (and (clo? clo1)
             (clo? clo2)
             (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
             (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2))))))
  
  ;
  ; Environment
  ;
  
  (struct env (lst) #:transparent)
  
  (define (make-new-env)
    (env `((random . ,meta-random-address))))
  
  (define (add-var-to-env old-env var adr)
    (let ((old-lst (env-lst old-env)))
      (env (cons (cons var adr) old-lst))))
  
  (define (contains-env? lst)
    (cond ((null? lst) #f)
          ((env? (car lst)) #t)
          (else (contains-env? (cdr lst)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                       Predefined functions                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Random
  ;
  
  (define PSEUDO_RANDOM_GENERATOR_STATE '#(2816165110 2738388292 45348490 3966956132 40780214 47365848))
  
  (define (create-random-generator)
    (vector->pseudo-random-generator PSEUDO_RANDOM_GENERATOR_STATE))
  
  (define PSEUDO_RANDOM_GENERATOR (create-random-generator))
  
  (define meta-random-address 0)
  (define pseudo-random-generator-address 1)
  
  (define pseudo-random (clo (lam '(max)
                                  `((random max pseudo-random-generator)))
                             (env `((pseudo-random-generator . ,pseudo-random-generator-address)))))
  (define regular-random (clo (lam '(max)
                                   '((random max)))
                              (env '())))
  
  (define meta-random (if IS_DEBUGGING
                          pseudo-random
                          regular-random))
  
  (define (reset-random-generator!)
    (set! PSEUDO_RANDOM_GENERATOR (create-random-generator)))
  
  (define (set-pseudo-random-generator! new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR_STATE (pseudo-random-generator->vector new-pseudo-random-generator)))
  
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
  
  (struct trace-key (label
                     parent-id
                     id
                     guard-ids) #:transparent)
  
  (struct label-trace-key trace-key (debug-info) #:transparent)
  
  (define (make-guard-trace-key label parent-id guard-ids)
    (trace-key label parent-id (new-trace-id!) guard-ids))
  
  (define (make-label-trace-key label debug-info)
    (let ((new-id (new-trace-id!)))
      (label-trace-key label new-id new-id '() debug-info)))
  
  (define (make-mp-tail-trace-key label parent-id)
    (trace-key label parent-id (new-trace-id!) '()))
  
  ;
  ; Trace nodes
  ;
  
  (struct trace-node (trace-key
                      trace
                      (children #:mutable)
                      (executions #:mutable)))
  
  (define (make-generic-trace-node constructor trace-key trace)
    (constructor trace-key trace '() '()))
  
  (struct label-trace trace-node ())
  (struct guard-trace trace-node ())
  (struct mp-tail-trace trace-node ())
  
  (define (make-label-trace trace-key trace)
    (make-generic-trace-node label-trace trace-key trace))
  
  (define (make-guard-trace trace-key trace)
    (make-generic-trace-node guard-trace trace-key trace))
  
  (define (make-mp-tail-trace trace-key trace)
    (make-generic-trace-node mp-tail-trace trace-key trace))
  
  (define (add-execution! trace-node)
    (let ((old-executions (trace-node-executions trace-node))
          (time (current-seconds)))
      (set-trace-node-executions! trace-node (cons time old-executions))))
  
  ;
  ; Tracer context
  ;
  
  (struct tracer-context (is-tracing?
                          trace-key
                          current-trace-length
                          trace-nodes
                          trace-nodes-dictionary
                          labels-encountered
                          trace-nodes-executing
                          splits-cf-id-stack
                          continuation-calls-stack
                          closing-function
                          mp-tails-dictionary
                          merges-cf-function) #:transparent #:mutable)
  
  (define GLOBAL_TRACER_CONTEXT #f)
  
  (define (new-tracer-context)
    (tracer-context #f
                    #f
                    0
                    '()
                    (new-dictionary = 100 (lambda (label-trace-id) label-trace-id))
                    '()
                    '()
                    (new-stack)
                    (new-stack)
                    #f
                    (new-dictionary = 100 (lambda (splits-cf-id) splits-cf-id))
                    #f))
  
  (define (is-tracing?)
    (tracer-context-is-tracing? GLOBAL_TRACER_CONTEXT))
  
  (define (is-tracing-label? label)
    (and (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)
         (equal? (trace-key-label (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)) label)))
  
  (define (is-tracing-guard?)
    (let ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT)))
      (not (eq? (trace-key-guard-ids trace-key) '()))))
  
  (define (add-trace-length! n)
    (let ((current-length (tracer-context-current-trace-length GLOBAL_TRACER_CONTEXT)))
      (set-tracer-context-current-trace-length! GLOBAL_TRACER_CONTEXT (+ current-length n))))
  
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
    (let ((pair (massoc label (tracer-context-labels-encountered GLOBAL_TRACER_CONTEXT))))
      (if pair
          (set-mcdr! pair (+ (mcdr pair) 1))
          (set-tracer-context-labels-encountered! GLOBAL_TRACER_CONTEXT 
                                                  (cons (mcons label 1) (tracer-context-labels-encountered GLOBAL_TRACER_CONTEXT))))))
  
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
  
  (define (push-splits-cf-id! splits-cf-id)
    (push! (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT) splits-cf-id))
  
  (define (pop-splits-cf-id!)
    (pop! (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT)))
  
  (define (top-splits-cf-id)
    (top (tracer-context-splits-cf-id-stack GLOBAL_TRACER_CONTEXT)))
  
  ;
  ; Trace node executing stack
  ;
  
  (define (pop-trace-node-executing!)
    (let ((trace-nodes-executing (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
      (if (null? trace-nodes-executing)
          (error "Trace-nodes-executing stack is empty!")
          (set-tracer-context-trace-nodes-executing! GLOBAL_TRACER_CONTEXT
                                                     (cdr trace-nodes-executing)))))
  
  (define (push-trace-node-executing! trace-node)
    (let ((trace-nodes-executing (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
      (set-tracer-context-trace-nodes-executing! GLOBAL_TRACER_CONTEXT
                                                 (cons trace-node trace-nodes-executing))))
  
  (define (top-trace-node-executing)
    (let ((trace-nodes-executing (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
      (if (null? trace-nodes-executing)
          (error "Trace-nodes-executing stack is empty!")
          (car trace-nodes-executing))))
  
  ;
  ; Continuation (call/cc stack)
  ;
  
  (define (pop-continuation!)
    (pop! (tracer-context-continuation-calls-stack GLOBAL_TRACER_CONTEXT)))
  
  (define (push-continuation! k)
    (push! (tracer-context-continuation-calls-stack GLOBAL_TRACER_CONTEXT) k))
  
  (define (top-continuation)
    (top (tracer-context-continuation-calls-stack GLOBAL_TRACER_CONTEXT)))
  
  ;
  ; Trace frames stack
  ;
  
  (define (pop-trace-frame!)
    (pop-trace-node-executing!)
    (pop-continuation!))
  
  (define (pop-trace-frame-until-label! label)
    (let ((current-trace-node-executing (top-trace-node-executing)))
      (define (loop current-trace-node-executing)
        (unless (equal? (trace-key-label (trace-node-trace-key current-trace-node-executing)) label)
          (pop-trace-frame!)
          (loop (top-trace-node-executing))))
      (loop current-trace-node-executing)))
  
  (define (pop-trace-node-frame-from-stack! label)
    ;;Keep popping the trace frames from the stack until the top of the stack is the trace frame for this label.
    ;;Then pop one more time to get it off the stack.
    (when (not (null? (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
      (pop-trace-frame-until-label! label)
      (pop-trace-frame!)))
  
  (define (push-trace-frame! trace-node-executing continuation)
    (push-trace-node-executing! trace-node-executing)
    (push-continuation! continuation))
  
  ;
  ; Start tracing
  ;
  
  (define (start-tracing-guard! guard-id old-trace-key)
    (clear-trace!)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-guard-function))
    (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-guard-merges-cf-function))
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #t)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-guard-trace-key (trace-key-label old-trace-key)
                                                                               (trace-key-parent-id old-trace-key)
                                                                               (append (trace-key-guard-ids old-trace-key) (list guard-id)))))
  
  (define (start-tracing-label! label debug-info)
    (clear-trace!)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-label-function))
    (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-label-merges-cf-function))
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #t)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-label-trace-key label debug-info)))
  
  ;
  ; Stop tracing
  ;
  
  (define (make-stop-tracing-guard-function)
    (define (stop-tracing-guard! trace looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key))
             (parent-id (trace-key-parent-id trace-key))
             (guard-ids (trace-key-guard-ids trace-key))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-guard-trace-function parent-id looping?))))
        (add-guard-trace! label parent-id guard-ids transformed-trace)))
    stop-tracing-guard!)
  
  (define (make-stop-tracing-label-function)
    (define (stop-tracing-label! trace looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-label-trace-function looping?))))
        (add-label-trace! trace-key transformed-trace)))
    stop-tracing-label!)
  
  (define (make-stop-tracing-mp-tail-function mp-id)
    (define (stop-tracing-mp-tail! mp-tail looping?)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (parent-id (trace-key-parent-id trace-key))
             (label (trace-key-label trace-key))
             (transformed-mp-tail (transform-and-optimize-trace mp-tail (make-transform-mp-tail-trace-function parent-id looping?))))
        (add-mp-tail-trace! mp-id trace-key transformed-mp-tail)))
    stop-tracing-mp-tail!)
  
  (define (stop-tracing-bookkeeping!)
    (set-tracer-context-is-tracing?! GLOBAL_TRACER_CONTEXT #f)
    (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT #f)
    (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT #f)
    (clear-trace!))
  
  (define (stop-tracing-abnormal!)
    (stop-tracing-bookkeeping!)
    (flush-ast-nodes-traced!))
  
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
  
  (define (return-if-existing trace . errormessage)
    (if trace
        trace
        (apply error errormessage)))
  
  ;guard-ids should go from the top of the tree to the bottom
  (define (search-guard-trace label guard-ids)
    (let ((first-trace-node (get-label-trace label)))
      (define (find-next-node-in-path trace-node guard-id)
        (define (loop children)
          (cond ((null? children) #f)
                ((equal? (trace-key-label (trace-node-trace-key (car children))) guard-id) (car children))
                (else (loop (cdr children)))))
        (loop (trace-node-children trace-node)))
      (define (follow-path trace-node guard-ids)
        (if (null? guard-ids)
            trace-node
            (follow-path (find-next-node-in-path trace-node (car guard-ids)) (cdr guard-ids))))
      (follow-path first-trace-node guard-ids)))
  
  ;; Looks at the current trace-nodes-executing stack and creates a trace-key containing the label
  ;; that is the ancestor of any new guard-trace that would be created, as well as the path from
  ;; this label to the new guard-trace through the trace tree.
  (define (get-path-to-new-guard-trace)
    (let* ((list (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
      (define (loop list path)
        ;(display "list = ") (display list) (display "; path = ") (display path) (newline)
        (cond ((null? list) '())
              ((label-trace? (car list)) (make-guard-trace-key (trace-key-label (trace-node-trace-key (car list)))
                                                               (trace-key-parent-id (trace-node-trace-key (car list)))
                                                               path))
              ((mp-tail-trace? (car list)) (make-guard-trace-key (trace-key-label (trace-node-trace-key (car list)))
                                                                 (trace-key-parent-id (trace-node-trace-key (car list)))
                                                                 path))
              (else (loop (cdr list) (cons (trace-key-label (trace-node-trace-key (car list))) path)))))
      (loop list '())))
  
  (define (get-guard-trace guard-id)
    (let* ((old-trace-key (get-path-to-new-guard-trace))
           (label (trace-key-label old-trace-key))
           (parent-guards (trace-key-guard-ids old-trace-key))
           (all-guards (append parent-guards (list guard-id)))
           (trace-node-found (search-guard-trace label all-guards)))
      (return-if-existing trace-node-found "Guard-trace not found!" all-guards)))
  
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
      (return-if-existing trace-node-found "Mp-tail-trace not found!" mp-id)))
  
  ;
  ; Adding traces
  ;
  
  (define (take-all-but-last lst)
    (reverse (cdr (reverse lst))))
  
  (define (add-guard-trace! label parent-id guard-ids trace)
    (let* ((parent-trace-node (search-guard-trace label (take-all-but-last guard-ids)))
           (new-guard-id (last guard-ids))
           (new-guard-trace-key (make-guard-trace-key new-guard-id parent-id guard-ids)))
      (write-guard-trace new-guard-id trace)
      (if (not parent-trace-node)
          (error "Trace-key was not found: " new-guard-trace-key)
          (set-trace-node-children! parent-trace-node
                                    (cons (make-guard-trace new-guard-trace-key trace)
                                          (trace-node-children parent-trace-node))))))
  
  (define (add-label-trace! trace-key transformed-trace)
    (let* ((label (trace-key-label trace-key))
           (debug-info (label-trace-key-debug-info trace-key))
           (trace-id (trace-key-id trace-key))
           (label-trace (make-label-trace trace-key transformed-trace)))
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
    (let* ((old-trace-key (get-path-to-new-guard-trace))
           (label (trace-key-label old-trace-key))
           (guards (trace-key-guard-ids old-trace-key)))
      (trace-exists? (search-guard-trace label (append guards (list guard-id))))))
  
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
  
  (define (trace-tree-rec f trace-node)
    (for-each (lambda (child)
                (f child)
                (trace-tree-rec f child))
              (trace-node-children trace-node)))
  
  (define (map-over-trace-tree f)
    (for-each (lambda (trace-node)
                (f trace-node)
                (trace-tree-rec f trace-node))
              (tracer-context-trace-nodes GLOBAL_TRACER_CONTEXT)))
  
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
      (table-for-each (lambda (key mp-tail)
                        (add-trace-length! mp-tail)
                        (trace-tree-rec add-trace-length! mp-tail))
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
      (table-for-each (lambda (key mp-tail)
                        (add-trace-node-execution-info mp-tail)
                        (trace-tree-rec add-trace-node-execution-info mp-tail))
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
                    ;The environment should be saved and restored
                    (let ((pair (mcons (car trace) #t)))
                      (first-run (cdr trace) (cdr stack) (cons pair first-run-through))))
                   (else 
                    (let ((pair (mcons (car trace) #f)))
                      ;Not really necessary to add the pair to the first-run-through list
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
         (remove-continuation)
         new-state)))
  
  (define (make-transform-guard-trace-looping label-trace-id)
    (define (transform-guard-trace-looping trace)
      `(letrec ((non-loop ,(append '(lambda ()) trace)))
         (non-loop)
         ;(output "----------- EXECUTING TRACE ") (output ',label) (output " -----------") (output-newline)
         (call-label-trace! ,label-trace-id)))
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
  ;                                      Trace merging/execution                                         ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Merging traces
  ;
  
  (define (make-guard-merges-cf-function)
    (define (guard-merges-cf! trace)
      (let* ((trace-key-to-trace (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key-to-trace))
             (parent-id (trace-key-parent-id trace-key-to-trace))
             (guard-ids (trace-key-guard-ids trace-key-to-trace))
             (transformed-trace (transform-and-optimize-trace trace transform-trace-non-looping-plain)))
        (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (lambda (trace looping?) '()))
        (set-tracer-context-trace-key! GLOBAL_TRACER_CONTEXT (make-mp-tail-trace-key label parent-id))
        (add-guard-trace! label parent-id guard-ids transformed-trace)))
    guard-merges-cf!)
  
  (define (make-label-merges-cf-function)
    (define (label-merges-cf! trace)
      (let ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
            (transformed-trace (transform-and-optimize-trace trace transform-trace-non-looping-plain))) ;(make-transform-label-trace-function #f))))
        (add-label-trace! trace-key transformed-trace)))
    label-merges-cf!)
  
  (define (make-mp-tail-merges-cf-function mp-id)
    (define (mp-tail-merges-cf! trace)
      (let* ((trace-key (tracer-context-trace-key GLOBAL_TRACER_CONTEXT))
             (label (trace-key-label trace-key))
             (transformed-trace (transform-and-optimize-trace trace transform-trace-non-looping-plain))) ;(make-transform-mp-tail-trace-function label #f))))
        (add-mp-tail-trace! mp-id trace-key transformed-trace)))
    mp-tail-merges-cf!)
  
  ;
  ; Executing traces
  ;
  
  (define (call-label-trace! label-trace-id)
    (let* ((label-trace (find (tracer-context-trace-nodes-dictionary GLOBAL_TRACER_CONTEXT) label-trace-id))
           (label (trace-key-label (trace-node-trace-key label-trace))))
      (execute `(pop-trace-node-frame-from-stack! ',label))
      (execute-label-trace label)))
  
  (define (trace-node-frame-on-stack? label)
    (define (loop list)
      (cond ((null? list) #f)
            ((or (label-trace? (car list))
                 (mp-tail-trace? (car list)))
             (equal? label (trace-key-label (trace-node-trace-key (car list)))))
            (else (loop (cdr list)))))
    (loop (tracer-context-trace-nodes-executing GLOBAL_TRACER_CONTEXT)))
  
  (define (execute-guard-trace guard-id)
    (let* ((guard-trace (get-guard-trace guard-id))
           (trace (trace-node-trace guard-trace))
           (old-trace-key (get-path-to-new-guard-trace))
           (corresponding-label (trace-key-label old-trace-key)))
      (add-execution! guard-trace)
      (execute `(let* ((value (call/cc (lambda (k)
                                         (push-trace-frame! ,guard-trace k)
                                         (eval ,trace)))))
                  (when (trace-node-frame-on-stack? ',corresponding-label)
                    (pop-trace-node-frame-from-stack! ',corresponding-label))
                  (let ((kk (top-continuation)))
                    (kk value))))))
  
  (define (execute-label-trace label)
    (let* ((label-trace (get-label-trace label))
           (trace (trace-node-trace label-trace)))
      (add-execution! label-trace)
      (execute `(let ((label-value (call/cc (lambda (k)
                                              (push-trace-frame! ,label-trace k)
                                              (eval ,trace)))))
                  (pop-trace-frame!)
                  label-value))))
  
  (define (execute-mp-tail-trace mp-id)
    (let* ((mp-tails-dictionary (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
           (mp-tail-trace (get-mp-tail-trace mp-id))
           (trace (trace-node-trace mp-tail-trace)))
      (add-execution! mp-tail-trace)
      (if trace
          (let ((mp-value (call/cc (lambda (k)
                                     (push-trace-frame! mp-tail-trace k)
                                     (eval trace)))))
            (pop-trace-frame!)
            (let ((kk (top-continuation)))
              (kk mp-value)))
          (error "Trace for merge point was not found; mp id: " mp-id))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Running evaluator                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Evaluator/trace instructions
  ;
  
  (define (guard-false guard-id e)
    (if v
        (begin (output "Guard-false failed") (output-newline) (bootstrap-to-ev guard-id e))
        (begin (output "Guard passed") (output-newline))))
  
  (define (guard-true guard-id e)
    (if v
        (begin (output "Guard passed") (output-newline))
        (begin (output "Guard-true failed") (output-newline) (bootstrap-to-ev guard-id e))))
  
  (define (guard-same-closure clo i guard-id)
    (when (not (clo-equal? v clo))
      (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output v) (output-newline)
      (bootstrap-to-ko guard-id (closure-guard-failedk i))))
  
  (define (guard-same-nr-of-args i rator guard-id)
    (let ((current-i (length v)))
      (when (not (= i current-i))
        (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
        (bootstrap-to-ko (cons guard-id current-i) (apply-failedk rator current-i)))))
  
  (define (save-val)
    (when (env? v)
      (error "Save-val: saved an environment instead of a val!"))
    (set! θ (cons v θ)))
  
  (define (save-vals i)
    (when (contains-env? v)
      (error "Save-vals: saved an environment instead of a val!"))
    (set! θ (append (take v i) θ))
    (set! v (drop v i)))
  
  (define (save-all-vals)
    (when (contains-env? v)
      (error "Save-all-vals: saved an environment instead of a val!"))
    (set! θ (append v θ)))
  
  (define (save-env)
    (set! θ (cons ρ θ)))
  
  (define (set-env ρ*)
    (set! ρ ρ*))
  
  (define (restore-env)
    (set! ρ (car θ))
    (set! θ (cdr θ)))
  
  (define (restore-val)
    (set! v (car θ))
    (when (env? v)
      (error "Restore-val: restored an environment instead of a val!"))
    (set! θ (cdr θ)))
  
  (define (restore-vals i)
    (set! v (take θ i))
    (when (contains-env? v)
      (error "Restore-vals: restored an environment instead of a val!"))
    (set! θ (drop θ i)))
  
  (define (alloc-var x)
    (let ((a (new-gencounter!)))
      (set! ρ (add-var-to-env ρ x a))
      (insert! σ a v)))
  
  (define (set-var x)
    (let ((a (cdr (assoc x (env-lst ρ)))))
      (insert! σ a v)))
  
  (define (debug)
    (= 1 1))
  
  (define (lookup-var x)
    (when (eq? x 'debug) (debug))
    (let ((binding (assoc x (env-lst ρ))))
      (match binding
        ((cons _ a) (set! v (find σ a)))
        (_ (set! v (eval x))))))
  
  (define (create-closure x es)
    (set! v (clo (lam x es) ρ)))
  
  (define (literal-value e)
    (set! v e))
  
  (define (quote-value e)
    (set! v e))
  
  (define (apply-native i)
    (let ((rands (take θ i)))
      (when (contains-env? rands)
        (error "Apply-native: rands contains an environment"))
      (set! θ (drop θ i))
      (set! v (apply v rands))))
  
  (define (add-continuation φ)
    (set! τ-κ (cons φ τ-κ)))
  
  (define (remove-continuation)
    (set! τ-κ (cdr τ-κ)))
  
  (define (switch-to-clo-env i)
    (let ((clo v))
      (restore-vals i)
      (save-env)
      (save-vals i)
      (set-env (clo-ρ clo))))
  
  (define (run-trace ms)
    (for/last ((instruction ms))
      (eval instruction)))
  
  (define (append-trace ms)
    (when τ
      (let ((new-instructions-length (length ms)))
        (set! τ (append (reverse ms) τ))
        (add-trace-length! new-instructions-length)
        (when (> (tracer-context-current-trace-length GLOBAL_TRACER_CONTEXT) MAX_TRACE_LENGTH)
          (display "##### MAX TRACE LENGTH REACHED #####") (newline)
          (stop-tracing-abnormal!)))))
  
  (define (execute . ms)
    (when (is-tracing?)
      (append-trace ms))
    (run-trace ms))
  
  ;
  ; Evaluation
  ;
  
  (define (eval-seq es κ)
    (match es
      ('()
       (execute `(literal-value '())
                `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((list e)
       (ev e κ))
      ((cons e es)
       (execute `(save-env)
                `(add-continuation ,(seqk es)))
       (ev e (cons (seqk es) κ)))))
  
  (define (do-function-call i κ)
    (match v
      ((clo (lam x es) ρ)
       (execute `(switch-to-clo-env ,i))
       (let loop ((i i) (x x))
         (match x
           ('()
            (unless (= i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i))
            (execute `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ)))
           ((cons x xs)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
            (execute `(restore-val)
                     `(alloc-var ',x))
            (loop (- i 1) xs))
           ((? symbol? x)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) "case 3"))
            (execute `(restore-vals ,i)
                     `(alloc-var ',x)
                     `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ))))))
      (_
       (execute `(apply-native ,i)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))))
  
  (define (step state)
    (match state
      ((ev `(and ,e . ,es) κ)
       (execute `(add-continuation ,(andk es)))
       (ev e (cons (andk es) κ)))
      ((ev `(apply ,rator ,args) κ)
       (execute `(add-continuation ,(applyk rator)))
       (ev args (cons (applyk rator) κ)))
      ((ev (? symbol? x) (cons φ κ))
       (execute `(lookup-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(begin ,es ...) κ)
       (eval-seq es κ))
      ((ev `(can-close-loop ,e) κ)
       (execute `(add-continuation ,(can-close-loopk)))
       (ev e (cons (can-close-loopk) κ)))
      ((ev `(can-start-loop ,e ,debug-info) κ)
       (execute `(add-continuation ,(can-start-loopk e '())))
       (ev debug-info (cons (can-start-loopk e '()) κ)))
      ((ev `(cond) (cons φ κ))
       (execute `(literal-value ())
                `(remove-continuation))
       (ko φ κ))      
      ((ev `(cond (else . ,es)) κ)
       (eval-seq es κ))
      ((ev `(cond (,pred . ,pes) . ,es) κ)
       (execute `(save-env)
                `(add-continuation ,(condk pes es)))
       (ev pred (cons (condk pes es) κ)))
      ((ev `(define ,pattern . ,expressions) κ)
       (if (symbol? pattern)
           (begin (execute `(save-env)
                           `(add-continuation ,(definevk pattern)))
                  (ev (car expressions) (cons (definevk pattern) κ)))
           (begin (execute `(alloc-var ',(car pattern))
                           `(create-closure ',(cdr pattern) ',expressions)
                           `(set-var ',(car pattern))
                           `(remove-continuation))
                  (match κ
                    ((cons φ κ) (ko φ κ))))))
      ((ev `(if ,e ,e1 . ,e2) κ)
       (execute `(save-env)
                `(add-continuation ,(ifk e1 e2)))
       (ev e (cons (ifk e1 e2) κ)))
      ((ev `(is-evaluating ,e) κ)
       (execute `(add-continuation ,(is-evaluatingk)))
       (ev e (cons (is-evaluatingk) κ)))
      ((ev `(lambda ,x ,es ...) (cons φ κ))
       (execute `(create-closure ',x ',es)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(let () . ,expressions)  κ)
       (eval-seq expressions κ))
      ((ev `(let ((,var ,val) . ,bds) . ,es) κ)
       (unless (null? bds)
         (error "Syntax error: let used with more than one binding: " bds))
       (execute `(save-env)
                `(add-continuation ,(letk var es)))
       (ev val (cons (letk var es) κ)))
      ((ev `(let* () . ,expressions) κ)
       (eval-seq expressions κ))
      ((ev `(let* ((,var ,val) . ,bds) . ,es) κ)
       (execute `(save-env)
                `(add-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ev `(letrec ((,x ,e) . ,bds) . ,es) κ)
       (execute `(literal-value '())
                `(alloc-var ',x)
                `(save-env)
                `(add-continuation ,(letreck x bds es)))
       (ev e (cons (letreck x bds es) κ)))
      ((ev `(or ,e . ,es) κ)
       (execute `(add-continuation ,(ork es)))
       (ev e (cons (ork es) κ)))
      ((ev `(quote ,e) (cons φ κ))
       (execute `(quote-value ',e)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(set! ,x ,e) κ)
       (execute `(save-env)
                `(add-continuation ,(setk x)))
       (ev e (cons (setk x) κ)))
      ((ev `(,rator) κ)
       (execute `(save-env)
                `(add-continuation ,(ratork 0 'regular-nulary)))
       (ev rator (cons (ratork 0 'regular-nulary) κ)))
      ((ev `(,rator . ,rands) κ)
       (execute `(save-env))
       (let ((rrands (reverse rands)))
         (execute `(add-continuation ,(randk rator (cdr rrands) 1)))
         (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
      ((ev e (cons φ κ))
       (execute `(literal-value ,e)
                `(remove-continuation))
       (ko φ κ))
      ((ko (andk '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (andk '()) (cons φ κ))
       (execute `(remove-continuation))
       (ko φ κ))
      ((ko (andk es) κ)
       (if v
           (begin (execute `(add-continuation ,(andk (cdr es))))
                  (ev (car es) (cons (andk (cdr es)) κ)))
           (begin (execute `(remove-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (applicationk debug) κ)
       (execute `(restore-env)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (apply-failedk rator i) κ)
       (execute `(save-all-vals)
                `(save-env)
                `(add-continuation ,(ratork i 'apply)))
       (ev rator (cons (ratork i 'apply) κ)))
      ((ko (applyk rator) κ)
       (let ((i (length v)))
         (execute `(guard-same-nr-of-args ,i ',rator ,(inc-guard-id!))
                  `(save-all-vals)
                  `(save-env)
                  `(add-continuation ,(ratork i 'apply)))
         (ev rator (cons (ratork i 'apply) κ))))
      ((ko (closure-guard-failedk i) κ)
       (do-function-call i κ))
      ((ko (condk pes '()) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) '()))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                           `(literal-value '())
                           `(remove-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (condk pes `((else . ,else-es))) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',`(begin ,@else-es)))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes)))
                  (eval-seq else-es κ))))
      ((ko (condk pes `((,pred . ,pred-es) . ,es)) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',`(cond ,@es)))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                           `(save-env)
                           `(add-continuation ,(condk pred-es es)))
                  (ev pred (cons (condk pred-es es) κ)))))
      ((ko (definevk x) (cons φ κ))
       (execute `(restore-env)
                `(alloc-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ko (haltk) _)
       #f) 
      ((ko (ifk e1 e2) κ)
       (execute `(restore-env))
       (let ((new-guard-id (inc-guard-id!)))
         (if v
             (begin (execute `(guard-true ,new-guard-id ',(if (null? e2)
                                                              '()
                                                              (car e2)))) ;If the guard fails, the predicate was false, so e2 should be evaluated
                    (ev e1 κ))
             (begin (execute `(guard-false ,new-guard-id ',e1)) ;If the guard fails, the predicate was true, so e1 should be evaluated
                    (if (null? e2)
                        (begin (execute `(remove-continuation)
                                        `(literal-value '()))
                               (ko (car κ) (cdr κ)))
                        (ev (car e2) κ))))))
      ((ko (letk x es) κ)
       (execute `(restore-env)
                `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x '() es) κ)
       (execute `(restore-env)
                `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x `((,var ,val) . ,bds) es) κ)
       (execute `(restore-env)
                `(alloc-var ',x)
                `(save-env)
                `(add-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ko (letreck x '() es) κ)
       (execute `(restore-env)
                `(set-var ',x))
       (eval-seq es κ))
      ((ko (letreck x `((,var ,val) . ,bds) es) κ)
       (execute `(restore-env)
                `(set-var ',x)
                `(alloc-var ',var)
                `(save-env)
                `(add-continuation ,(letreck var bds es)))
       (ev val (cons (letreck var bds es) κ)))
      ((ko (ork '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (ork es) κ)
       (if v
           (begin (execute `(remove-continuation))
                  (ko (car κ) (cdr κ)))
           (ev `(or ,@es) κ)))
      ((ko (randk rator '() i) κ)
       (execute `(restore-env)
                `(save-val)
                `(save-env)
                `(add-continuation ,(ratork i 'regular)))
       (ev rator (cons (ratork i 'regular) κ)))
      ((ko (randk rator rands i) κ)
       (execute `(restore-env)
                `(save-val)
                `(save-env)
                `(add-continuation ,(randk rator (cdr rands) (+ i 1))))
       (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
      ((ko (ratork i debug) κ)
       (execute `(restore-env)
                `(guard-same-closure ,v ,i  ,(inc-guard-id!)))
       (do-function-call i κ))
      ((ko (seqk '()) (cons φ κ)) ;TODO No tailcall optimization!
       (execute `(restore-env)
                `(remove-continuation))
       (ko φ κ))
      ((ko (seqk (cons e exps)) κ)
       (execute `(add-continuation ,(seqk exps)))
       (ev e (cons (seqk exps) κ)))
      ((ko (setk x) (cons φ κ))
       (execute `(restore-env)
                `(set-var ',x)
                `(remove-continuation))
       (ko φ κ))))
  
  (define (step* s)
    (match s
      ((ko (haltk) _)
       v)
      ((ko (is-evaluatingk) (cons φ κ))
       (execute `(remove-continuation))
       (set-root-expression-if-uninitialised! v)
       (when (is-tracing?)
           (add-ast-node-traced! v))
       (step* (ko φ κ)))
      ((ev `(splits-control-flow) (cons φ κ))
       (execute `(remove-continuation)
                `(push-splits-cf-id! ,(inc-splits-cf-id!)))
       (step* (ko φ κ)))
      ((ev `(merges-control-flow) (cons φ κ))
       (let ((mp-id (top-splits-cf-id)))
         (execute `(remove-continuation)
                  `(pop-splits-cf-id!))
         (if (is-tracing?)
             (begin 
               (when (is-tracing-guard?)
                 (append-trace `((pop-trace-frame!))))
               (append-trace `((pop-trace-frame!)
                               (execute-mp-tail-trace ,mp-id)))
               ((tracer-context-merges-cf-function GLOBAL_TRACER_CONTEXT) (reverse τ))
               (if (mp-tail-trace-exists? mp-id)
                   (begin (stop-tracing-normal!)
                          (let ((new-state (eval `(execute-mp-tail-trace ,mp-id))))
                            (step* new-state)))
                   (begin (clear-trace!)
                          (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-mp-tail-function mp-id))
                          (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-mp-tail-merges-cf-function mp-id))
                          (step* (ko φ κ)))))
             (step* (ko φ κ)))))
      ((ko (can-close-loopk) (cons φ κ))
       (output "closing annotation: tracing loop ") (output v) (output-newline)
       (when (is-tracing-label? v)
         (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
         (stop-tracing! #f))
       (execute `(remove-continuation))
       (step* (ko φ κ)))
      ((ko (can-start-loopk label '()) κ)
       (execute `(add-continuation ,(can-start-loopk '() v)))
       (step* (ev label (cons (can-start-loopk '() v) κ))))
      ((ko (can-start-loopk '() debug-info) (cons φ κ))
       (cond ((is-tracing-label? v)
              (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
              (stop-tracing! #t)
              (let ((new-state (execute-label-trace v)))
                (step* new-state)))
             ;((and (label-trace-exists? v) (not (is-tracing?)))
             ((label-trace-exists? v)
              (output "----------- EXECUTING TRACE -----------") (output-newline)
              (let ((new-state (execute-label-trace v)))
                (step* new-state)))
             ((and (not (is-tracing?)) (>= (get-times-label-encountered v) TRACING_THRESHOLD))
              (output "----------- STARTED TRACING -----------") (output-newline)
              (start-tracing-label! v debug-info)
              (execute `(remove-continuation))
              (let ((new-state (ko φ κ)))
                (step* new-state)))
             (else
              (execute `(remove-continuation))
              (inc-times-label-encountered! v)
              (when (is-tracing?)
                (output "----------- ALREADY TRACING ANOTHER LABEL -----------") (output-newline))
              (let ((new-state (ko φ κ)))
                (step* new-state)))))
      (_
       (let ((new-state (step s)))
         (step* new-state)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                           Bootstrapping                                              ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (switch-to-trace-guard! guard-id old-trace-key)
    (clear-trace!)
    (start-tracing-guard! guard-id old-trace-key))
  
  (define (bootstrap guard-id state)
    (output "------ BOOTSTRAP: FULL GUARD PATH: ") (output (get-path-to-new-guard-trace)) (output " ------") (output-newline)
    (cond ((guard-trace-exists? guard-id)
           (output "----------- STARTING FROM GUARD ") (output guard-id) (output " -----------") (output-newline)
           (execute-guard-trace guard-id))
          ((not (is-tracing?))
           (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
           (let* ((old-trace-key (get-path-to-new-guard-trace))
                  (corresponding-label (trace-key-label old-trace-key)))
             (pop-trace-node-frame-from-stack! corresponding-label)
             (let ((kk (top-continuation)))
               (start-tracing-guard! guard-id old-trace-key)
               (kk state))))
          (else
           (output "----------- CANNOT TRACE GUARD ") (output guard-id)
           (output " ; ALREADY TRACING ANOTHER LABEL -----------") (output-newline)
           (let* ((old-trace-key (get-path-to-new-guard-trace))
                  (corresponding-label (trace-key-label old-trace-key)))
             (pop-trace-node-frame-from-stack! corresponding-label)
             (let ((kk (top-continuation)))
               (switch-to-trace-guard! guard-id old-trace-key)
               (kk state))))))
  
  (define (bootstrap-to-ev guard-id e)
    (bootstrap guard-id (ev e τ-κ)))
  
  (define (bootstrap-to-ko guard-id φ)
    (bootstrap guard-id (ko φ τ-κ)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Starting evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Resetting evaluator
  ;
  
  (define (reset!)
    (set! ρ (make-new-env))
    (set! σ (new-store))
    (set! θ '())
    (set! τ '())
    (set! τ-κ `(,(haltk)))
    (set! GLOBAL_TRACER_CONTEXT (new-tracer-context))
    (reset-metrics!)
    (reset-random-generator!)
    (reset-trace-outputting!))
  
  (define (clear-trace!)
    (set-tracer-context-current-trace-length! GLOBAL_TRACER_CONTEXT 0)
    (set! τ '()))
  
  ;
  ; Starting evaluator
  ;
  
  (define (inject e)
    (ev e `(,(haltk))))
  
  (define (run s)
    (reset!)
    (apply step* (list (let ((v (call/cc (lambda (k)
                                           (push-continuation! k)
                                           s))))
                         v))))
  
  (define (start)
    (run (inject (read)))))