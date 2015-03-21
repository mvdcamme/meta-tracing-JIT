(module instruction-set racket
  
  (require "interaction.scm"
           "output.scm")
  
  (provide (all-defined-out))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                    Evaluator/trace instructions                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; A counter used to generate id's for newly allocated variables.
  ;;; This id is then used as the address in the environment.
  (define gencounter 2)
  (define (new-gencounter!)
    (let ((temp gencounter))
      (set! gencounter (+ gencounter 1))
      temp))
  
  ;;; Check the value of the register v. If it is #f, do nothing, else handle this guard failure.
  (define (guard-false program-state guard-id e)
    (if (program-state-v program-state)
        (begin (output "Guard-false failed") (output-newline) (guard-failed-with-ev guard-id e))
        (begin (output "Guard passed") (output-newline) program-state)))
  
  ;;; Check the value of the register v. If it is #t, do nothing, else handle this guard failure.
  (define (guard-true program-state guard-id e)
    (if (program-state-v program-state)
        (begin (output "Guard passed") (output-newline) program-state)
        (begin (output "Guard-true failed") (output-newline) (guard-failed-with-ev guard-id e))))
  
  ;;; Check whether the register v currently contains the same closure as it did when this guard
  ;;; was recorded. If it does, do nothing, else handle this guard failure.
  (define (guard-same-closure program-state clo i guard-id)
    (if (clo-equal? (program-state-v program-state) clo)
        program-state
        (begin (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output (program-state-v program-state)) (output-newline)
               (guard-failed-with-ko guard-id (closure-guard-failedk i)))))
  
  ;;; Check whether the register v currently contains a list that has the same length as it did
  ;;; when this guard was recorded. If it does, do nothing, else handle this guard failure.
  (define (guard-same-nr-of-args program-state i rator guard-id)
    (let ((current-i (length (program-state-v program-state))))
      (if (= i current-i)
          program-state
          (begin (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
                 (guard-failed-with-ko (cons guard-id current-i) (apply-failedk rator current-i))))))
  
  ;;; Save the value in the register v to the stack θ.
  (define (save-val program-state)
    (let ((v (program-state-v program-state))
          (θ (program-state-θ program-state)))
      (when (env? v)
        (error "Save-val: saved an environment instead of a val!"))
      (program-state-copy program-state (θ (cons v θ)))))
  
  ;;; Save the first i elements of the list currently stored in the register v to the stack θ
  ;;; and drop these elements from the list in v.
  (define (save-vals program-state i)
    (let ((v (program-state-v program-state))
          (θ (program-state-θ program-state)))
      (when (contains-env? v)
        (error "Save-vals: saved an environment instead of a val!"))
      (program-state-copy program-state
                          (θ (append (take v i) θ))
                          (v (drop v i)))))
  
  ;;; Save all elements of the list currently stored in the register v to the stack θ.
  (define (save-all-vals program-state)
    (let ((v (program-state-v program-state))
          (θ (program-state-θ program-state)))
      (when (contains-env? v)
        (error "Save-all-vals: saved an environment instead of a val!"))
      (program-state-copy program-state
                          (θ (append v θ)))))
  
  ;;; Save the environment currently stored in ρ to the stack θ.
  (define (save-env program-state)
    (let ((ρ (program-state-ρ program-state))
          (θ (program-state-θ program-state)))
      (program-state-copy program-state
                          (θ (cons ρ θ)))))
  
  ;;; Replace the environment currently stored in ρ by ρ*.
  (define (set-env program-state ρ*)
    (let ((ρ (program-state-ρ program-state)))
      (program-state-copy program-state
                          (ρ ρ*))))
  
  ;;; Pop the environment from the stack θ and store it in ρ.
  (define (restore-env program-state)
    (let ((ρ (program-state-ρ program-state))
          (θ (program-state-θ program-state)))
      (program-state-copy program-state
                          (ρ (car θ))
                          (θ (cdr θ)))))
  
  ;;; Pop the first value from the stack θ and store it in the register v.
  (define (restore-val program-state)
    (let ((v (program-state-v program-state))
          (θ (program-state-θ program-state)))
      (when (env? (car θ))
        (error "Restore-val: restored an environment instead of a val!"))
      (program-state-copy program-state
                          (v (car θ))
                          (θ (cdr θ)))))
  
  ;;; Pop the first i values from the stack θ and store them in the form of a list in the register v.
  (define (restore-vals program-state i)
    (let ((v (program-state-v program-state))
          (θ (program-state-θ program-state)))
      (when (contains-env? (take θ i))
        (error "Restore-vals: restored an environment instead of a val!"))
      (program-state-copy program-state
                          (v (take θ i))
                          (θ (drop θ i)))))
  
  ;;; Allocate a new variable in the environment and the store with the name x and
  ;;; as current value, the value in the register v.
  (define (alloc-var program-state x)
    (let ((a (new-gencounter!))
          (ρ (program-state-ρ program-state))
          (σ (program-state-σ program-state)))
      (program-state-copy program-state
                          (ρ (add-var-to-env ρ x a))
                          (σ (cons (cons a v) σ)))))
  
  ;;; Assign the value currently in the register v to the variable x.
  (define (set-var program-state x)
    (let* ((ρ (program-state-ρ program-state))
           (σ (program-state-σ program-state))
           (a (cdr (assoc x (env-lst ρ)))))
      (program-state-copy program-state
                          (σ (cons a v) σ))))
  
  ;;; Used for debugging, allows you to place a breakpoint, stopping the debugger whenever this
  ;;; function is called.
  (define (debug)
    (= 1 1))
  
  ;;;  Looks up the current value of the variable x and stores in the register v.
  (define (lookup-var program-state x)
    (let ((ρ (program-state-ρ program-state))
          (σ (program-state-σ program-state)))
      ;; If the variable currently evaluated was called 'debug', call the debug function.
      ;; This is especially useful for meta-level debugging: interesting locations in the code
      ;; of the meta-level interpreter canbe debugged by simply using the variable 'debug.
      (when (eq? x 'debug) (debug))
      (let ((binding (assoc x (env-lst ρ))))
        (match binding
          ((cons _ a) (program-state-copy program-state
                                          (v (cdr (assoc σ a)))))
          (_ (program-state-copy program-state
                                 (v (eval x))))))))
  
  ;;; Creates a closure with the arguments x, and the body es and places this new closure
  ;;; in the register v.
  (define (create-closure program-state x es)
    (let ((ρ (program-state-ρ program-state)))
      (program-state-copy program-state
                          (v (clo (lam x es) ρ)))))
  
  ;;; Place the value e in the register v.
  (define (literal-value program-state e)
    (program-state-copy program-state
                        (v e)))
  
  ;;; Place the value e in the register v.
  (define (quote-value program-state e)
    (program-state-copy program-state
                        (v e)))
  
  ;;; Apply the native procedure currently stored in the register v to the first
  ;;; i values on the stack θ.
  (define (apply-native program-state i)
    (let* ((v (program-state-v program-state))
           (θ (program-state-θ program-state))
           (rands (take θ i)))
      (when (contains-env? rands)
        (error "Apply-native: rands contains an environment"))
      (program-state-copy program-state
                          (θ (drop θ i))
                          (v (apply v rands))))))