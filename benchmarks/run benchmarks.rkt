#lang racket
(require (file "../slip tracing interpreter.scm"))

(define BENCHMARK_INPUT_PATH "input_file.scm")

;
; Interpreters
;
(define rec-slip-interpreter-normal-path "slip interpreters/base rec interpreter.scm")
(define rec-slip-interpreter-traced-path "slip interpreters/traced rec interpreter merging.scm")

(define rec-slip-interpreter-normal-exp (file->value rec-slip-interpreter-normal-path))
(define rec-slip-interpreter-traced-exp (file->value rec-slip-interpreter-traced-path))

;
; Benchmarks
;
(define bubble-sort-benchmark-path "bubble-sort.scm")
(define blur-benchmark-path "blur.scm")
(define boyer-benchmark-path "boyer.scm")
(define browse-benchmark-path "browse.scm")
(define churchnums-benchmark-path "churchnums.scm")
(define collatz-benchmark-path "collatz.scm")
(define cpstak-benchmark-path "cpstak.scm")
(define eta-benchmark-path "eta.scm")
(define fac-benchmark-path "fac.scm")
(define fib-benchmark-path "fib.scm")
(define kcfa-2-benchmark-path "kcfa2.scm")
(define kcfa-3-benchmark-path "kcfa3.scm")
(define kcfa-worst-case-40-benchmark-path "kcfa-worst-case-40.scm")
(define loop-2-benchmark-path "loop2.scm")
(define meta-circ-benchmark-path "meta-circ.scm")
(define mj09-benchmark-path "mj09.scm")
(define nqueens-benchmark-path "nqueens.scm")
(define nqueens-2-benchmark-path "nqueens 2.scm")
(define pnpoly-benchmark-path "pnpoly.scm")
(define primtest-benchmark-path "primtest.scm")
(define regex-benchmark-path "regex.scm")
(define rotate-benchmark-path "rotate.scm")
(define rotate-2-benchmark-path "rotate 2.scm")
(define rsa-benchmark-path "rsa.scm")
(define sat-benchmark-path "sat.scm")
(define scheme2c-benchmark-path "scheme2c.scm")
(define scheme2java-benchmark-path "scm2java.scm")
(define simple-guard-trace-merging-benchmark-path "simple guard-trace merging.scm")
(define simplified-trace-explosion-benchmark-path "simplified trace-explosion.scm")
(define solovay-strassen-benchmark-path "solovay-strassen.scm")
(define trace-explosion-benchmark-path "trace-explosion.scm")
(define trace-explosion-not-random-benchmark-path "trace-explosion not random.scm")
(define tree-sort-benchmark-path "tree-sort.scm")
(define towers-of-hanoi-benchmark-path "towers-of-hanoi.scm")



;
; Benchmarking
;

(define output display)
(define (output-newline)
  (output #\newline))

(define (output-metric metric-name result)
  (output "Metric ") (output metric-name) (output " got result ") (output result)
  (output-newline))

(define (output-result benchmark-file evaluator result)
  (output "=> ") (output evaluator) (output " evaluated ") (output benchmark-file) (output " and got result: ") (output result)
  (output-newline)
  (output-newline))

(define (overwrite-input-file new-benchmark-path)
  (let* ((input-port (open-input-file new-benchmark-path))
         (output-port (open-output-file BENCHMARK_INPUT_PATH #:exists 'replace))
         (benchmark-file-contents (read input-port)))
    (write benchmark-file-contents output-port)
    (close-input-port input-port)
    (close-output-port output-port)))

(define (run-benchmark benchmark-path)
  (let* ((s-exp (file->value benchmark-path))
         (tracing-interpreter-name "Tracing interpreter")
         (rec-slip-interpreter-normal-name "Recursive Slip interpreter (normal)")
         (rec-slip-interpreter-traced-name "Recursive Slip interpreter (traced)"))
    (define (run-interpreter interpreter-start-function interpreter-name)
      (output-interpreter-start interpreter-name)
      (let ((value (interpreter-start-function)))
        (output-result-from-evaluator interpreter-name value)))
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
      (run-interpreter (lambda () (eval rec-slip-interpreter-normal-exp)) rec-slip-interpreter-normal-name))
    (define (run-rec-slip-interpreter-traced)
      (run-interpreter (lambda () (run (inject rec-slip-interpreter-traced-exp))) rec-slip-interpreter-traced-name))
    
    (define (run-metrics)
      (let ((total-number-of-traces-metric-name "total-number-of-traces")
            (average-trace-length-metric-name "average-trace-length")
            (trace-duplication-metric-name "trace-duplicity")
            (trace-executions-metric-name "trace-executions"))
        (define (run-total-number-of-traces-metric)
          (output-metric total-number-of-traces-metric-name (calculate-total-number-of-traces)))
        (define (run-average-trace-length-metric)
          (output-metric average-trace-length-metric-name (calculate-average-trace-length)))
        (define (run-trace-executions-metric)
          (output-metric trace-executions-metric-name (get-trace-executions)))
        ;(define (run-trace-duplication-metric)
         ; (output-metric trace-duplication-metric-name (calculate-duplicity)))
        (run-total-number-of-traces-metric)
        (run-average-trace-length-metric)
        (run-trace-executions-metric)))
        ;(run-trace-duplication-metric)))
    
    (output-benchmark-start)
    (overwrite-input-file benchmark-path)
    
    (run-tracing-interpreter)
    (run-rec-slip-interpreter-normal)
    (run-rec-slip-interpreter-traced)
    
    (run-metrics)
    
    (output-benchmark-end)))

