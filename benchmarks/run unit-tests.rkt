(module unit-tests racket
  
  (require (file "benchmark-paths.rkt"))
  (require (file "run benchmarks.rkt"))
  
  (run-benchmarks (list fac-benchmark-path
                        fib-benchmark-path
                        rsa-benchmark-path
                        nqueens-benchmark-path
                        rotate-benchmark-path
                        simplified-trace-explosion-benchmark-path
                        scheme2c-benchmark-path
                        simple-guard-trace-merging-benchmark-path)))