(module run-benchmarks racket
  
  (provide run-benchmark
           run-benchmarks
           run-nested-benchmark
           run-nested-benchmarks)
  
  (require racket/date)
  (require racket/include)
  
  (require (file "../file-outputting.scm"))
  (require (file "../evaluator.scm"))
  ;(require (file "../slip tracing interpreter.scm"))
  (require (file "benchmark-paths.rkt"))
  
  ;(namespace-require 'racket/base)
  ;(namespace-require (build-path "../slip tracing interpreter.scm"))
  
  (define BENCHMARK_INPUT_PATH "input_file.scm")
  (define NESTED_BENCHMARK_INPUT_PATH "input_file_nested.scm")
  (define NESTED_SLIP_INTERPRETERS_FOLDER "./Nested interpretation/")
  (define SLIP_INTERPRETERS_FOLDER "./Slip interpreters/")
           
  ;
  ; Interpreters
  ;
  (define rec-interpreter-direct-path (string-append SLIP_INTERPRETERS_FOLDER "Rec interpreter direct.scm"))
  (define rec-interpreter-traced-merging-path (string-append SLIP_INTERPRETERS_FOLDER "Rec interpreter traced merging.scm"))
  (define rec-interpreter-traced-merging-duplication-path (string-append SLIP_INTERPRETERS_FOLDER "Rec interpreter traced merging duplication.scm"))
  (define rec-interpreter-traced-no-merging-path (string-append SLIP_INTERPRETERS_FOLDER "Rec interpreter traced no merging.scm"))
  (define rec-interpreter-traced-no-merging-duplication-path (string-append SLIP_INTERPRETERS_FOLDER "Rec interpreter traced no merging duplication.scm"))
  
  (define rec-interpreter-direct-exp (file->value rec-interpreter-direct-path))
  (define rec-interpreter-traced-merging-exp (file->value rec-interpreter-traced-merging-path))
  (define rec-interpreter-traced-merging-duplication-exp (file->value rec-interpreter-traced-merging-duplication-path))
  (define rec-interpreter-traced-no-merging-exp (file->value rec-interpreter-traced-no-merging-path))
  (define rec-interpreter-traced-no-merging-duplication-exp (file->value rec-interpreter-traced-no-merging-duplication-path))
  
  (define nested-interpreter-path (string-append NESTED_SLIP_INTERPRETERS_FOLDER "Rec interpreter direct.scm"))
  
  ;
  ; Output file
  ;
  
  (define BASE_OUTPUT_FILE_NAME "./Benchmarking output/output")
  (define BASE_OUTPUT_EXTENSION "txt")
  
  (define OUTPUT_FILE_NAME (make-full-output-file-name BASE_OUTPUT_FILE_NAME BASE_OUTPUT_EXTENSION))
  
  (define (append-to-output-file text)
    (append-to-file OUTPUT_FILE_NAME text))
  
  ;
  ; Benchmarking
  ;
  
  (define (output-aux text console-output-function)
    (console-output-function text)
    (append-to-output-file text))
  
  (define (output text)
    (output-aux text display))
  
  (define (output-newline)
    (output #\newline))
  
  (define (output-pretty text)
    (output-aux text pretty-print))
  
  (define (output-metric metric-name result)
    (output "Metric ") (output metric-name) (output " got result ") (output result)
    (output-newline))
  
  (define (output-result benchmark-file evaluator result)
    (output "=> ") (output evaluator) (output " evaluated ") (output benchmark-file) (output " and got result: ") (output result)
    (output-newline)
    (output-newline))
  
  (define (overwrite-input-file benchmark-input-path new-benchmark-path)
    (let* ((input-port (open-input-file new-benchmark-path))
           (output-port (open-output-file benchmark-input-path #:exists 'replace))
           (benchmark-file-contents (read input-port)))
      (write benchmark-file-contents output-port)
      (close-input-port input-port)
      (close-output-port output-port)))
  
;  (define (run-trace-metrics)
;    (let ((total-number-of-traces-metric-name "total-number-of-traces")
;          (average-trace-length-metric-name "average-trace-length")
;          (trace-duplication-metric-name "trace-duplicity")
;          (trace-executions-metric-name "trace-executions"))
;      (define (run-total-number-of-traces-metric)
;        (output-metric total-number-of-traces-metric-name (calculate-total-number-of-traces)))
;      (define (run-average-trace-length-metric)
;        (output-metric average-trace-length-metric-name (calculate-average-trace-length)))
;      (define (run-trace-executions-metric)
;        (define (show-times-executed result)
;          (output "label-traces ") (output (apply + (map (lambda (executions) (length (cdr executions)))
;                                                         (car result))))
;          (output-newline)
;          (output "guard-traces ") (output (apply + (map (lambda (executions) (length (cdr executions)))
;                                                         (cadr result))))
;          (output-newline)
;          (output "mp-tail-traces ") (output (apply + (map (lambda (executions) (length (cdr executions)))
;                                                           (caddr result))))
;          (output-newline))
;        (output "Metric ") (output trace-executions-metric-name) (output " calculated results: ") (output-newline)
;        (show-times-executed (get-trace-executions))
;        (output-newline))
;      (define (run-trace-duplication-metric)
;        (let* ((trace-duplication-metric-result (calculate-trace-duplication)))
;          (if (pair? trace-duplication-metric-result)
;              (let ((root-expression (car trace-duplication-metric-result))
;                    (all-ast-nodes (cadr trace-duplication-metric-result))
;                    (average #f)
;                    (variation #f)
;                    (standard-deviation #f)
;                    (min-trace-duplication +inf.0)
;                    (max-trace-duplication -inf.0))
;                (define (process-ast-nodes-list ast-nodes)
;                  (let ((n 0.0)
;                        (sum-1 0.0)
;                        (sum-2 0.0))
;                    (for ((ast-node ast-nodes))
;                      (let* ((labels-traced (vector-ref ast-node 1))
;                             (ast-node-trace-duplication (length labels-traced)))
;                        (when (> ast-node-trace-duplication 0)
;                          (set! n (+ n 1))
;                          (set! min-trace-duplication (min min-trace-duplication ast-node-trace-duplication))
;                          (set! max-trace-duplication (max max-trace-duplication ast-node-trace-duplication))
;                          (set! sum-1 (+ ast-node-trace-duplication sum-1))
;                          (set! sum-2 (+ (sqr ast-node-trace-duplication) sum-2)))))
;                    (set! average (/ sum-1 n))
;                    (set! variation (- (/ sum-2 n) (sqr average)))
;                    (set! standard-deviation (sqrt variation))))
;                (process-ast-nodes-list all-ast-nodes)
;                (output-pretty root-expression) (newline)
;                (output-metric trace-duplication-metric-name (list (cons 'average average)
;                                                                   (cons 'variation variation)
;                                                                   (cons 'standard-deviation standard-deviation)
;                                                                   (cons 'minimum-trace-duplication min-trace-duplication)
;                                                                   (cons 'maximum-trace-duplication max-trace-duplication))))
;              (output-metric trace-duplication-metric-name trace-duplication-metric-result))))
;      (run-total-number-of-traces-metric)
;      (run-average-trace-length-metric)
;      (run-trace-executions-metric)
;      (run-trace-duplication-metric)
;      (output-newline)
;      (output-newline)))
  
  (define (start-benchmark benchmark-path)
    (let* ((s-exp (file->value benchmark-path))
           (tracing-interpreter-name "Tracing interpreter")
           (rec-slip-interpreter-normal-name "Recursive Slip interpreter (normal)")
           (rec-slip-interpreter-traced-name "Recursive Slip interpreter (traced)")
           (rec-slip-interpreter-traced-no-merging-name "Recursive Slip interpreter (traced no merging)"))
      (define (run-interpreter interpreter-start-function interpreter-name)
        (output-interpreter-start interpreter-name)
        (let ((value (interpreter-start-function)))
          (output-result-from-evaluator interpreter-name value)))
      (define (run-interpreter-timed interpreter-start-function interpreter-name)
        (let ((start-ms (current-milliseconds)))
          (run-interpreter interpreter-start-function interpreter-name)
          (let* ((end-ms (current-milliseconds))
                 (delta-ms (- end-ms start-ms)))
            ;; Safeguard for 32-bit systems
            (if (> delta-ms 0)
                (begin (output "Time taken for ") (output interpreter-name) (output ": ") (output delta-ms) (output "ms") (output-newline))
                (error "Timing the run of the interpreter failed: calculated a negative time" delta-ms)))))
      (define (output-result-from-evaluator evaluator result)
        (output-result benchmark-path evaluator result))
      (define (output-benchmark-start)
        (output "---------- BENCHMARK STARTED: ") (output benchmark-path) (output " ----------")
        (output-newline)
        (output-newline))
      (define (output-benchmark-end)
        (output "---------- BENCHMARK FINISHED: ") (output benchmark-path) (output " ----------")
        (output-newline))
      (define (output-interpreter-start interpreter-name)
        (output "interpreter started: ") (output interpreter-name)
        (newline))
      (define (run-tracing-interpreter)
        (run-interpreter (lambda () (run (inject s-exp))) tracing-interpreter-name))
      (define (run-rec-slip-interpreter-normal)
        (run-interpreter (lambda () (eval rec-interpreter-direct-exp)) rec-slip-interpreter-normal-name))
      (define (run-rec-slip-interpreter-normal-meta-interpreted)
        (run-interpreter (lambda () (eval rec-interpreter-direct-exp)) rec-slip-interpreter-normal-name))
      (define (run-rec-slip-interpreter-traced-meta-interpreted)
        (run-interpreter-timed (lambda () (run (inject rec-interpreter-traced-merging-duplication-exp))) rec-slip-interpreter-traced-name))
      (define (run-rec-slip-interpreter-traced-no-merging-meta-interpreted)
        (run-interpreter-timed (lambda () (run (inject rec-interpreter-traced-no-merging-duplication-exp))) rec-slip-interpreter-traced-no-merging-name))
      
      (output-benchmark-start)
      
      (run-tracing-interpreter)
      (run-rec-slip-interpreter-normal)
      
      ;(run-rec-slip-interpreter-traced-meta-interpreted)
      ;(run-trace-metrics)
      
      (run-rec-slip-interpreter-traced-meta-interpreted)
      ;(run-trace-metrics)
      
      (output-benchmark-end)))
  
  (define (run-benchmark benchmark-path)
    (overwrite-input-file BENCHMARK_INPUT_PATH benchmark-path)
    (start-benchmark benchmark-path))
  
  (define (run-nested-benchmark benchmark-path)
    (overwrite-input-file BENCHMARK_INPUT_PATH nested-interpreter-path)
    (overwrite-input-file NESTED_BENCHMARK_INPUT_PATH benchmark-path)
    (start-benchmark benchmark-path))
  
  (define (run-benchmarks-aux run-benchmark-function n benchmarks)
    (for ((i (range n)))
      ;(set-pseudo-random-generator! (current-pseudo-random-generator))
      (for ((benchmark benchmarks))
        (run-benchmark-function benchmark)))
    "Finished!")
  
  (define (run-benchmarks n benchmarks)
    (run-benchmarks-aux run-benchmark n benchmarks))
  
  (define (run-nested-benchmarks n benchmarks)
    (run-benchmarks-aux run-nested-benchmark n benchmarks)))
