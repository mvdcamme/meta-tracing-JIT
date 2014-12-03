#lang racket
(require (file "../slip tracing interpreter.scm"))

(define BENCHMARK_INPUT_PATH "input_file.scm")

;
; Interpreters
;
(define rec-slip-interpreter-path "rec slip meta-interpreter.scm")

(define rec-slip-interpreter-exp (file->value rec-slip-interpreter-path))

;
; Benchmarks
;
(define fac-benchmark-path "fac.scm")



;
; Benchmarking
;

(define (output benchmark-file evaluator result)
  (display evaluator) (display " evaluated ") (display benchmark-file) (display " and got result: ") (display result)
  (newline))

(define (overwrite-input-file new-benchmark-path)
  (let* ((input-port (open-input-file new-benchmark-path))
         (output-port (open-output-file BENCHMARK_INPUT_PATH #:exists 'replace))
         (benchmark-file-contents (read input-port)))
    (write benchmark-file-contents output-port)
    (close-input-port input-port)
    (close-output-port output-port)))

(define (run-benchmark benchmark-path)
  (let* ((s-exp (file->value benchmark-path)))
    (define (output-result-from-evaluator evaluator result)
      (output benchmark-path evaluator result))
    (define (run-racket)
      (eval s-exp))
    (define (run-tracing-interpreter)
      (run (inject s-exp)))
    (define (run-rec-slip-interpreter-normal)
      (eval rec-slip-interpreter-exp))
    (define (run-rec-slip-interpreter-traced)
      (run (inject rec-slip-interpreter-exp)))
    (overwrite-input-file benchmark-path)
    (output-result-from-evaluator "Racket" (run-racket))
    (output-result-from-evaluator "Tracing interpreter" (run-tracing-interpreter))
    (output-result-from-evaluator "Recursive Slip interpreter (normal)" (run-rec-slip-interpreter-normal))
    (output-result-from-evaluator "Recursive Slip interpreter (traced)" (run-rec-slip-interpreter-traced))))

