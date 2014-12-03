#lang racket
(require (file "../slip tracing interpreter.scm"))

(define BENCHMARK_INPUT_PATH "input_file.scm")

;
; Interpreters
;
(define rec-slip-interpreter-normal-path "rec slip meta-interpreter normal.scm")
(define rec-slip-interpreter-traced-path "rec slip meta-interpreter traced.scm")

(define rec-slip-interpreter-normal-exp (file->value rec-slip-interpreter-normal-path))
(define rec-slip-interpreter-traced-exp (file->value rec-slip-interpreter-traced-path))

;
; Benchmarks
;
(define bubble-sort-benchmark-path "bubble-sort.scm")
(define fac-benchmark-path "fac.scm")
(define fib-benchmark-path "fib.scm")
(define nqueens-2-benchmark-path "nqueens 2.scm")
(define rotate-2-benchmark-path "rotate 2.scm")
(define trace-explosion-benchmark-path "trace-explosion.scm")
(define tree-sort-benchmark-path "tree-sort.scm")
(define towers-of-hanoi-benchmark-path "towers-of-hanoi.scm")



;
; Benchmarking
;

(define output display)
(define output-newline newline)

(define (output-result benchmark-file evaluator result)
  (output evaluator) (output " evaluated ") (output benchmark-file) (output " and got result: ") (output result)
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
      (output "----- BENCHMARK STARTED: ") (output benchmark-path) (output " -----")
      (output-newline))
    (define (output-benchmark-end)
      (output "----- BENCHMARK FINISHED: ") (output benchmark-path) (output " -----")
      (output-newline))
    (define (output-interpreter-start interpreter-name)
      (output "--- interpreter started: ") (output interpreter-name) (output " ---")
      (newline))
    (define (run-tracing-interpreter)
      (run-interpreter (lambda () (run (inject s-exp))) tracing-interpreter-name))
    (define (run-rec-slip-interpreter-normal)
      (run-interpreter (lambda () (eval rec-slip-interpreter-normal-exp)) tracing-interpreter-name))
    (define (run-rec-slip-interpreter-traced)
      (run-interpreter (lambda () (run (inject rec-slip-interpreter-traced-exp))) tracing-interpreter-name))
    
    (output-benchmark-start)
    (overwrite-input-file benchmark-path)
    
    (run-tracing-interpreter)
    (run-rec-slip-interpreter-normal)
    (run-rec-slip-interpreter-traced)
    
    (output-benchmark-end)))

