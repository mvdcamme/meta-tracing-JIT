(module metrics racket
  
  (require "tracing.scm")
  
  (provide calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
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