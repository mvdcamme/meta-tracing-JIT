(module continuations racket
  
  (provide (all-defined-out))
  
  ;
  ; Continuations
  ;
  
  (struct andk (es) #:transparent)
  (struct apply-failedk (rator i) #:transparent)
  (struct applicationk (debug) #:transparent)
  (struct applyk (rator) #:transparent)
  (struct closure-guard-failedk (i) #:transparent)
  (struct condk (pes es) #:transparent)
  (struct definevk (x) #:transparent)
  (struct haltk () #:transparent)
  (struct ifk (e1 e2) #:transparent)
  (struct letk (x es) #:transparent)
  (struct let*k (x bds es) #:transparent)
  (struct let*k-done () #:transparent)
  (struct letreck (x bds es) #:transparent)
  (struct ork (es) #:transparent)
  (struct randk (e es i) #:transparent)
  (struct ratork (i debug) #:transparent)
  (struct seqk (es) #:transparent)
  (struct setk (x) #:transparent)
  
  ;
  ; Tracing annotations continuations
  ;
  
  ;;; The continuation to be followed after encountering a can-close-loop annotation.
  (struct can-close-loopk () #:transparent)
  
  ;;; The continuation to be followed after encountering a can-start-loop annotation.
  (struct can-start-loopk (label debug-info) #:transparent)
  
  ;;; The continuation to be followed after encountering a is-evaluating annotation.
  (struct is-evaluatingk () #:transparent)
  
  )