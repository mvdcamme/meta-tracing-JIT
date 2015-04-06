(module benchmark-paths racket
  
  (provide (all-defined-out))
  
  ;
  ; Benchmarks
  ;
  (define bubble-sort-benchmark-path "bubble-sort.scm")
  (define blur-benchmark-path "blur.scm")
  (define boyer-benchmark-path "boyer.scm")
  (define browse-benchmark-path "browse.scm")
  (define churchnums-benchmark-path "churchnums.scm")
  (define closed-benchmark-path "closed.scm")
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
  (define pypy-trace-explosion-benchmark-path "pypy trace-explosion.scm")
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
  ; Nested interpretation benchmarks
  ;
  
  (define nested-fac-benchmark-path "Nested interpretation/fac.scm")
  (define nested-fib-benchmark-path "Nested interpretation/fib.scm")
  (define nested-simplified-trace-explosion-benchmark-path "Nested interpretation/simplified trace-explosion.scm")
  )