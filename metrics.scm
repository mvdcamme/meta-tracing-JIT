(module metrics racket
  
  (require "tracing.scm")
  
  (provide calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
           calculate-trace-duplication
           get-trace-executions)
  
  
  
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
    (for-each f (tracer-context-trace-nodes tracer-context)))
  
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
    (let ((label-traces '()))
      (define (add-trace-node-execution-info trace-node)
        (let ((binding (cons (trace-key-label (trace-node-trace-key trace-node)) (trace-node-executions trace-node))))
          (set! label-traces (cons binding label-traces))))
      (map-over-trace-tree tracer-context add-trace-node-execution-info)
      (list label-traces)))
  
  ;
  ; Resetting metrics
  ;
  
  (define (reset-metrics!)
    (reset-trace-duplication-metric!)))