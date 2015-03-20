(module closures racket
  
  (provide (all-defined-out))
  
  ;
  ; Closures
  ;
  
  (struct clo (λ ρ) #:transparent)
  (struct lam (x es) #:transparent)
  
  ;;; Checks whether two closures are equal.
  (define (clo-equal? clo1 clo2)
    (or (eq? clo1 clo2)
        (and (clo? clo1)
             (clo? clo2)
             (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
             (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2)))))))