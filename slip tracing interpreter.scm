(module tracing-interpreter racket
  (provide ;; Starting evaluator   
           inject
           run
           
           ;; Structs
           (struct-out ev)
           (struct-out ko)
           
           ;; Registers
           τ-κ
           
           ;; Trace instructions
           alloc-var
           apply-native
           bootstrap-to-evaluator
           call-global-continuation
           create-closure
           debug
           execute-trace
           execute-guard-trace
           execute-label-trace-with-id
           execute-label-trace-with-label
           execute-mp-tail-trace
           flush-label-traces-executing!
           guard-false
           guard-true
           guard-same-closure
           guard-same-nr-of-args
           literal-value
           lookup-var
           quote-value
           pop-continuation
           pop-splits-cf-id!
           pop-label-trace-executing!
           push-continuation
           push-splits-cf-id!
           push-label-trace-executing!
           restore-env
           restore-val
           restore-vals
           save-env
           save-all-vals
           save-val
           save-vals
           set-env
           set-var
           prepare-function-call
           top-splits-cf-id
           top-label-trace-executing
           
           ;; Metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length
           calculate-trace-duplication
           get-trace-executions
           
           
           ;; Purely for benchmarking the implementation
           set-pseudo-random-generator!)
  
  (require "dictionary.scm")
  (require "stack.scm")
  (require "tracing.scm")
  (require "trace-outputting.scm")
  
  (define (member-equal el lst)
    (cond ((null? lst) #f)
          ((equal? el (car lst)) lst)
          (else (member-equal el (cdr lst)))))
  
  ;
  ; Constants
  ;
  
  ;;; Determines whether all 'output'-statements effectively print their argument to the console
  ;;; or not.
  (define ENABLE_OUTPUT #f)
  
  ;;; Has the following effects:
  ;;;  - Provided the meta-traced interpreter uses the 'random' function defined on this level
  ;;;    (the tracing interpreter) when calling 'random' in the user-program, the random number
  ;;;    that is generated will be created based on a fixed, hardcoded pseudo-random generator state.
  ;;;    This means that the random numbers that are generated are always the same between program executions.
  (define IS_DEBUGGING #t)
  
  ;;; The amount of times a label needs to be encountered before it is considered 'hot'.
  (define TRACING_THRESHOLD 5)
  
  ;
  ; Outputting
  ;
  
  ;;; Prints the given argument to the console, if ENABLE_OUTPUT is set to #t.
  (define (output s)
    (when ENABLE_OUTPUT
      (display s)))
  
  ;;; Prints a newline to the console, if ENABLE_OUTPUT is set to #t.
  (define (output-newline)
    (output #\newline))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                             CK machine                                               ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; CK wrappers
  ;
  
  ;;; Represents the state of a program when evaluating an expression.
  ;;; It consists of an expression to be evaluated (e), and a list of continuations to be followed
  ;;; once the evaluation is complete (κ).
  (struct ev (e κ) #:transparent)
  
  ;;; Represents the state of a program when following a continuation.
  ;;; It consists of the continuation to be followed immediately (φ) and a list of continuations
  ;;; to be followed afterwards (κ).
  (struct ko (φ κ) #:transparent)
  
  ;
  ; Registers
  ;
  
  ;;; Stores the environment during program execution.
  (define ρ #f) ; env
  
  ;;; Stores the store during program execution.
  (define σ #f) ; store
  
  ;;; Stores the stack during program execution.
  (define θ #f) ; non-kont stack
  
  ;;; The general-purpose register used during program execution.
  (define v #f) ; value
  
  ;;; Stores the continuation stack during program execution.
  ;;; This stack is needed to switch back from trace execution to regular program interpretation.
  (define τ-κ #f) ;continuation stack
  
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
  (struct letreck (x bds es) #:transparent)
  (struct ork (es) #:transparent)
  (struct randk (e es i) #:transparent)
  (struct ratork (i debug) #:transparent)
  (struct seqk (es) #:transparent)
  (struct setk (x) #:transparent)
  
  
  ;;; A counter used to generate id's for newly allocated variables.
  ;;; This id is then used as the address in the environment.
  (define gencounter 2)
  (define (new-gencounter!)
    (let ((temp gencounter))
      (set! gencounter (+ gencounter 1))
      temp))
  
  ;;; Creates a new store that contains all predefined functions/variables.
  (define (new-store)
    (let ((dict (new-dictionary = 100 (lambda (splits-cf-id) splits-cf-id))))
      (insert! dict meta-random-address meta-random)
      (insert! dict pseudo-random-generator-address PSEUDO_RANDOM_GENERATOR)
      dict))
  
  ;
  ; Tracing annotations continuations
  ;
  
  ;;; The continuation to be followed after encountering a can-close-loop annotation.
  (struct can-close-loopk () #:transparent)
  
  ;;; The continuation to be followed after encountering a can-start-loop annotation.
  (struct can-start-loopk (label debug-info) #:transparent)
  
  ;;; The continuation to be followed after encountering a is-evaluating annotation.
  (struct is-evaluatingk () #:transparent)
  
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
             (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2))))))
  
  ;
  ; Environment
  ;
  
  ;;; Represents the environment used by the tracing interpreter.
  (struct env (lst) #:transparent)
  
  ;;; Creates a new environment 
  (define (make-new-env)
    (env `((random . ,meta-random-address))))
  
  (define (add-var-to-env old-env var adr)
    (let ((old-lst (env-lst old-env)))
      (env (cons (cons var adr) old-lst))))
  
  (define (contains-env? lst)
    (cond ((null? lst) #f)
          ((env? (car lst)) #t)
          (else (contains-env? (cdr lst)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                       Predefined functions                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Programs evaluated by the tracing interpreter do not start out with an empty environment.
  ;;; The environment is initiated with a number of predefined functions.
  
  ;
  ; Random
  ;
  
  (define PSEUDO_RANDOM_GENERATOR_STATE '#(2816165110 2738388292 45348490 3966956132 40780214 47365848))
  
  (define (create-random-generator)
    (vector->pseudo-random-generator PSEUDO_RANDOM_GENERATOR_STATE))
  
  (define PSEUDO_RANDOM_GENERATOR (create-random-generator))
  
  (define meta-random-address 0)
  (define pseudo-random-generator-address 1)
  
  (define pseudo-random (clo (lam '(max)
                                  `((random max pseudo-random-generator)))
                             (env `((pseudo-random-generator . ,pseudo-random-generator-address)))))
  (define regular-random (clo (lam '(max)
                                   '((random max)))
                              (env '())))
  
  (define meta-random (if IS_DEBUGGING
                          pseudo-random
                          regular-random))
  
  (define (reset-random-generator!)
    (set! PSEUDO_RANDOM_GENERATOR (create-random-generator)))
  
  (define (set-pseudo-random-generator! new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR new-pseudo-random-generator)
    (set! PSEUDO_RANDOM_GENERATOR_STATE (pseudo-random-generator->vector new-pseudo-random-generator)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                          Executing traces                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Recall that a trace is constructed in the form of a letrec-expression, e.g.,
  ;;; (letrec ((loop (lambda ()
  ;;;                  ...)))
  ;;;   (loop))
  
  ;;; Retrieve the actual instructions recorded in the trace from the given expression,
  ;;; i.e., the body of the lambda in the letrec-binding.
  (define (get-actual-trace letrec-expression)
    (cddr (cadr (car (cadr letrec-expression)))))
  
  ;;; Retrieves the instructions in the body of the letrec-expression.
  (define (get-letrec-body letrec-expression)
    (cddr letrec-expression))
  
  ;;; Returns the operator of an application.
  (define get-operator car)
  
  ;;; Executes a given trace. As mentioned above, this trace should be in the form of a letrec.
  (define (execute-trace s-expression)
    (let ((actual-trace (get-actual-trace s-expression))
          (letrec-body (get-letrec-body s-expression)))
      (define (execute-instruction instruction)
        (cond ((eq? (get-operator instruction) 'loop) (void))
              ((eq? (get-operator instruction) 'non-loop) (void))
              (else (eval instruction))))
      (define (execute-letrec-body instructions last-result)
        (cond ((null? instructions) last-result)
              ((eq? (get-operator (car instructions)) 'loop) (execute-trace s-expression))
              ((eq? (get-operator (car instructions)) 'non-loop) (execute-letrec-body (cdr instructions) last-result))
              (else (execute-letrec-body (cdr instructions) (eval (car instructions))))))
      (for-each execute-instruction actual-trace)
      (execute-letrec-body letrec-body '())))
  
  ;;; Executes the guard-trace associated with the given guard-id.
  (define (execute-guard-trace guard-id)
    (let* ((guard-trace (get-guard-trace guard-id))
           (trace (trace-node-trace guard-trace)))
      ;; Benchmarking: record the fact that this trace node will be executed
      (add-execution! guard-trace)
      (execute/trace `(let ()
                        (let* ((state (execute-trace ',trace))) ; Actually execute the trace
                          state)))))
  
  ;;; Executes the trace of the given label-trace-node.
  (define (execute-label-trace-with-trace-node tracer-context label-trace-node)
    (let ((trace (trace-node-trace label-trace-node)))
      ;; Benchmarking: record the fact that this trace node will be executed
      (add-execution! label-trace-node)
      (execute/trace `(let ()
                        ;; Push this trace-node on the stack of label-traces being executed
                        (push-label-trace-executing! ,tracer-context ,label-trace-node)
                        (let ((state (execute-trace ',trace))) ; Actually execute the trace
                          ;; Pop this trace-node again
                          (pop-label-trace-executing! ,tracer-context)
                          ;; Return the CK state
                          state)))))
  
  ;;; Execute the label-trace associated with the given id.
  (define (execute-label-trace-with-id tracer-context label-trace-id)
    (let ((label-trace-node (find (tracer-context-trace-nodes-dictionary tracer-context) label-trace-id)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  ;;; Execute the label-trace associated with the given label.
  (define (execute-label-trace-with-label tracer-context label)
    (let ((label-trace-node (get-label-trace tracer-context label)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  ;;; Execute the merge-point-tail-trace associated with the given merge-point-id.
  (define (execute-mp-tail-trace tracer-context mp-id state)
    (let* ((mp-tails-dictionary (tracer-context-mp-tails-dictionary tracer-context))
           (mp-tail-trace (get-mp-tail-trace mp-id))
           (label (trace-key-label (trace-node-trace-key mp-tail-trace)))
           (label-trace-node (get-label-trace label)))
      ;; It might be that a call to this mp-tail-trace has been recorded before the actual tracing
      ;; of this mp-tail was completed. In that case, it could be that the trace was never finished
      ;; (e.g., because it reached the maximum trace length).
      ;; So we have to check whether this mp-tail-trace actually exists.
      ;; If it doesn't, we jump back to regular interpretation with the given state.
      (if mp-tail-trace
          (begin (add-execution! mp-tail-trace)
                 (push-label-trace-executing-if-not-on-top! tracer-context label-trace-node)
                 (let ((state (execute-trace (trace-node-trace mp-tail-trace))))
                   ;; Pop this trace-node again
                   (pop-label-trace-executing! tracer-context)
                   state))
          (bootstrap-to-evaluator state))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                    Evaluator/trace instructions                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Check the value of the register v. If it is #f, do nothing, else handle this guard failure.
  (define (guard-false guard-id e)
    (if v
        (begin (output "Guard-false failed") (output-newline) (guard-failed-with-ev guard-id e))
        (begin (output "Guard passed") (output-newline))))
  
  ;;; Check the value of the register v. If it is #t, do nothing, else handle this guard failure.
  (define (guard-true guard-id e)
    (if v
        (begin (output "Guard passed") (output-newline))
        (begin (output "Guard-true failed") (output-newline) (guard-failed-with-ev guard-id e))))
  
  ;;; Check whether the register v currently contains the same closure as it did when this guard
  ;;; was recorded. If it does, do nothing, else handle this guard failure.
  (define (guard-same-closure clo i guard-id)
    (when (not (clo-equal? v clo))
      (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output v) (output-newline)
      (guard-failed-with-ko guard-id (closure-guard-failedk i))))
  
  ;;; Check whether the register v currently contains a list that has the same length as it did
  ;;; when this guard was recorded. If it does, do nothing, else handle this guard failure.
  (define (guard-same-nr-of-args i rator guard-id)
    (let ((current-i (length v)))
      (when (not (= i current-i))
        (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
        (guard-failed-with-ko (cons guard-id current-i) (apply-failedk rator current-i)))))
  
  ;;; Save the value in the register v to the stack θ.
  (define (save-val)
    (when (env? v)
      (error "Save-val: saved an environment instead of a val!"))
    (set! θ (cons v θ)))
  
  ;;; Save the first i elements of the list currently stored in the register v to the stack θ
  ;;; and drop these elements from the list in v.
  (define (save-vals i)
    (when (contains-env? v)
      (error "Save-vals: saved an environment instead of a val!"))
    (set! θ (append (take v i) θ))
    (set! v (drop v i)))
  
  ;;; Save all elements of the list currently stored in the register v to the stack θ.
  (define (save-all-vals)
    (when (contains-env? v)
      (error "Save-all-vals: saved an environment instead of a val!"))
    (set! θ (append v θ)))
  
  ;;; Save the environment currently stored in ρ to the stack θ.
  (define (save-env)
    (set! θ (cons ρ θ)))
  
  ;;; Replace the environment currently stored in ρ by ρ*.
  (define (set-env ρ*)
    (set! ρ ρ*))
  
  ;;; Pop the environment from the stack θ and store it in ρ.
  (define (restore-env)
    (set! ρ (car θ))
    (set! θ (cdr θ)))
  
  ;;; Pop the first value from the stack θ and store it in the register v.
  (define (restore-val)
    (set! v (car θ))
    (when (env? v)
      (error "Restore-val: restored an environment instead of a val!"))
    (set! θ (cdr θ)))
  
  ;;; Pop the first i values from the stack θ and store them in the form of a list in the register v.
  (define (restore-vals i)
    (set! v (take θ i))
    (when (contains-env? v)
      (error "Restore-vals: restored an environment instead of a val!"))
    (set! θ (drop θ i)))
  
  ;;; Allocate a new variable in the environment and the store with the name x and
  ;;; as current value, the value in the register v.
  (define (alloc-var x)
    (let ((a (new-gencounter!)))
      (set! ρ (add-var-to-env ρ x a))
      (insert! σ a v)))
  
  ;;; Assign the value currently in the register v to the variable x.
  (define (set-var x)
    (let ((a (cdr (assoc x (env-lst ρ)))))
      (insert! σ a v)))
  
  ;;; Used for debugging, allows you to place a breakpoint, stopping the debugger whenever this
  ;;; function is called.
  (define (debug)
    (= 1 1))
  
  ;;;  Looks up the current value of the variable x and stores in the register v.
  (define (lookup-var x)
    ;; If the variable currently evaluated was called 'debug', call the debug function.
    ;; This is especially useful for meta-level debugging: interesting locations in the code
    ;; of the meta-level interpreter canbe debugged by simply using the variable 'debug.
    (when (eq? x 'debug) (debug))
    (let ((binding (assoc x (env-lst ρ))))
      (match binding
        ((cons _ a) (set! v (find σ a)))
        (_ (set! v (eval x))))))
  
  ;;; Creates a closure with the arguments x, and the body es and places this new closure
  ;;; in the register v.
  (define (create-closure x es)
    (set! v (clo (lam x es) ρ)))
  
  ;;; Place the value e in the register v.
  (define (literal-value e)
    (set! v e))
  
  ;;; Place the value e in the register v.
  (define (quote-value e)
    (set! v e))
  
  ;;; Apply the native procedure currently stored in the register v to the first
  ;;; i values on the stack θ.
  (define (apply-native i)
    (let ((rands (take θ i)))
      (when (contains-env? rands)
        (error "Apply-native: rands contains an environment"))
      (set! θ (drop θ i))
      (set! v (apply v rands))))
  
  ;;; Push the continuation φ to the continuation stack τ-κ.
  (define (push-continuation φ)
    (set! τ-κ (cons φ τ-κ)))
  
  ;;; Pop the first continuation from the continuation stack τ-κ.
  (define (pop-continuation)
    (set! τ-κ (cdr τ-κ)))
  
  ;;; Prepares for an application of the closure currently stored in the register v
  ;;; by saving the current environment, popping the first i elements from the stack θ
  ;;; and switching to the lexical environment of the closure to be called.
  (define (prepare-function-call i)
    (let ((clo v))
      (restore-vals i)
      (save-env)
      (save-vals i)
      (set-env (clo-ρ clo))))
  
  ;;; Executes the given instructions by calling the Racket native 'eval' function on them and
  ;;; returns the last value that was evaluated.
  (define (eval-instructions ms)
    (for/last ((instruction ms))
      (eval instruction)))
  
  ;;; Executes the given instructions and records them into the trace, if the interpreter is
  ;;; currently tracing.
  (define (execute/trace tracer-context . ms)
    (when (is-tracing?)
      (append-trace! tracer-context ms))
    (eval-instructions ms))
  
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                     Handling tracing annotation                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Is-evaluating
  ;
  
  ;;; Handles the (is-evaluating expression) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  ;;; Used for benchmarking purposes.
  (define (handle-is-evaluating-annotation-reg tracer-context state)
    (execute/trace `(pop-continuation))
    (set-root-expression-if-uninitialised! v)
    (when (is-tracing?)
      (add-ast-node-traced! v))
    (run-evaluator tracer-context state))
  
  ;
  ; Starting/ending trace recording
  ;
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; evaluation with the given state.
  (define (handle-can-close-loop-annotation-reg tracer-context label state)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (execute/trace tracer-context `(pop-continuation))
    (run-evaluator tracer-context state))
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; evaluation with the given state.
  (define (handle-can-close-loop-annotation-tracing tracer-context label state)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (when (is-tracing-label? tracer-context label)
      (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
      (stop-tracing! #f))
    (execute/trace tracer-context `(pop-continuation))
    (run-evaluator tracer-context state))
  
  (define (check-stop-tracing-label tracer-context label state)
    (define (do-stop-tracing!)
      (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
      (stop-tracing! #t)
      (let ((new-state (execute-label-trace-with-label label)))
        (step* new-state)))
    (define (do-continue-tracing)
      (output "----------- CONTINUING TRACING -----------") (output-newline)
      (execute/trace `(pop-continuation))
      (step* state))
    (inc-times-label-encountered-while-tracing! tracer-context)
    (if (times-label-encountered-greater-than-threshold?)
        (do-stop-tracing!)
        (do-continue-tracing)))
  
  ;;; Handles the (can-start-loop label debug-info) annotation. If it is decided not to
  ;;; start executing the trace belonging to this label, regular interpretation continues
  ;;; with the given state.
  (define (handle-can-start-loop-annotation-reg tracer-context label debug-info state)
    ;; Continue evaluation with the given state.
    (define (continue-with-state)
      (execute/trace tracer-context `(pop-continuation))
      (run-evaluator tracer-context state))
    ;; Check whether it is worthwile to start tracing this label.
    ;; In this implementation, whether it is worthwile to trace a label only depends
    ;; on how hot the corresponding loop is: how many times has this label been encountered yet?
    (define (can-start-tracing-label?)
      (>= (get-times-label-encountered tracer-context label) TRACING_THRESHOLD))
          ;; We are currently tracing this label: check if this label refers to a 'true' loop.
    (cond ((label-trace-exists? tracer-context label)
           (output "----------- EXECUTING TRACE -----------") (output-newline)
           (let ((label-trace (get-label-trace tracer-context label)))
             ;; If we are already tracing, and this trace is a 'true' loop, we record
             ;; a jump to this already existing trace.
             ;; Else, we ignore the existing trace and just inline everything.
             (if (and (is-tracing?) (label-trace-loops? label-trace))
                 (let ((new-state (execute-label-trace-with-label label)))
                   (step* new-state))
                 (continue-with-state))))
          ;; We are not tracing anything at the moment, and we have determined that it
          ;; is worthwile to trace this label/loop, so start tracing.
          ((can-start-tracing-label?)
           (output "----------- STARTED TRACING -----------") (output-newline)
           (start-tracing-label! label debug-info)
           (continue-with-state))
          ;; We are already tracing and/or it is not worthwile to trace this label,
          ;; so continue regular interpretation. We do increase the counter for the number
          ;; of times this label has been encountered (i.e., we raise the 'hotness' of this loop).
          (else
           (inc-times-label-encountered! label)
           (when (is-tracing?)
             (output "----------- LABEL NOT HOT YET -----------") (output-newline))
           (continue-with-state))))
  
  ;;; Handles the (can-start-loop label debug-info) annotation. If it is decided not to
  ;;; start executing the trace belonging to this label, regular interpretation continues
  ;;; with the given state.
  (define (handle-can-start-loop-annotation-tracing tracer-context label debug-info state)
    ;; Continue evaluation with the given state.
    (define (continue-with-state)
      (execute/trace tracer-context `(pop-continuation))
      (run-evaluator tracer-context state))
    ;; Check whether it is worthwile to start tracing this label.
    ;; In this implementation, whether it is worthwile to trace a label only depends
    ;; on how hot the corresponding loop is: how many times has this label been encountered yet?
    (define (can-start-tracing-label?)
      (>= (get-times-label-encountered tracer-context label) TRACING_THRESHOLD))
          ;; We are currently tracing this label: check if this label refers to a 'true' loop.
    (cond ((is-tracing-label? tracer-context label)
           (check-stop-tracing-label tracer-context label state))
          ;; A trace for this label already exists, so start executing that trace?
          ((label-trace-exists? tracer-context label)
           (output "----------- EXECUTING TRACE -----------") (output-newline)
           (let ((label-trace (get-label-trace tracer-context label)))
             ;; If we are already tracing, and this trace is a 'true' loop, we record
             ;; a jump to this already existing trace.
             ;; Else, we ignore the existing trace and just inline everything.
             (if (and (is-tracing?) (label-trace-loops? label-trace))
                 (let ((new-state (execute-label-trace-with-label label)))
                   (step* new-state))
                 (continue-with-state))))
          ;; We are already tracing and/or it is not worthwile to trace this label,
          ;; so continue regular interpretation. We do increase the counter for the number
          ;; of times this label has been encountered (i.e., we raise the 'hotness' of this loop).
          (else
           (inc-times-label-encountered! label)
           (output "----------- ALREADY TRACING ANOTHER LABEL -----------") (output-newline)
           (continue-with-state))))
  
  ;
  ; Trace merging
  ;
  
  ;;; Handles the (merges-control-flow) annotation.
  (define (handle-merges-cf-annotation-reg tracer-context continuation)
    (output "MERGES CONTROL FLOW") (output-newline)
    (execute/trace tracer-context
                   `(pop-continuation)
                   `(pop-splits-cf-id! ,tracer-context))
    (run-evaluator tracer-context continuation))
  
  ;;; Handles the (merges-control-flow) annotation.
  (define (handle-merges-cf-annotation-tracing tracer-context continuation)
    (output "MERGES CONTROL FLOW") (output-newline)
    (let ((mp-id (top-splits-cf-id tracer-context)))
      (execute/trace `(pop-continuation)
                     `(pop-splits-cf-id! ,tracer-context))
      (begin
        (append-trace! tracer-context `((execute-mp-tail-trace ,mp-id ,continuation)))
        ((tracer-context-merges-cf-function tracer-context) (reverse τ))
        (if (mp-tail-trace-exists? mp-id)
            (begin (output "MP TAIL TRACE EXISTS") (output-newline)
                   (stop-tracing-normal!)
                   (let ((new-state (eval `(execute-mp-tail-trace ,mp-id ,continuation))))
                     (step* new-state)))
            (begin (output "MP TAIL TRACE DOES NOT EXIST") (output-newline)
                   (clear-trace! tracer-context)
                   (set-tracer-context-closing-function! tracer-context (make-stop-tracing-mp-tail-function mp-id))
                   (set-tracer-context-merges-cf-function! tracer-context (make-mp-tail-merges-cf-function mp-id))
                   (step* continuation))))))
  
  ;;; Handles the (splits-control-flow) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (handle-splits-cf-annotation-reg tracer-context state)
    (execute/trace tracer-context
                   `(pop-continuation)
                   `(push-splits-cf-id! tracer-context ,(inc-splits-cf-id!)))
    (run-evaluator tracer-context state))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Running evaluator                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (bootstrap-to-evaluator state)
    (call-global-continuation state))
  
  (define (eval-seq es κ)
    (match es
      ('()
       (execute/trace `(literal-value '())
                      `(pop-continuation))
       (ko (car κ) (cdr κ)))
      ((list e)
       (ev e κ))
      ((cons e es)
       (execute/trace `(save-env)
                `(push-continuation ,(seqk es)))
       (ev e (cons (seqk es) κ)))))
  
  (define (do-function-call i κ)
    (match v
      ((clo (lam x es) ρ)
       (execute/trace `(prepare-function-call ,i))
       (let loop ((i i) (x x))
         (match x
           ('()
            (unless (= i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i))
            (execute/trace `(push-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ)))
           ((cons x xs)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
            (execute/trace `(restore-val)
                           `(alloc-var ',x))
            (loop (- i 1) xs))
           ((? symbol? x)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) "case 3"))
            (execute/trace `(restore-vals ,i)
                           `(alloc-var ',x)
                           `(push-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ))))))
      (_
       (execute/trace `(apply-native ,i)
                      `(pop-continuation))
       (ko (car κ) (cdr κ)))))
  
  (define (step state)
    (match state
      ((ev `(and ,e . ,es) κ)
       (execute/trace `(push-continuation ,(andk es)))
       (ev e (cons (andk es) κ)))
      ((ev `(apply ,rator ,args) κ)
       (execute/trace `(push-continuation ,(applyk rator)))
       (ev args (cons (applyk rator) κ)))
      ((ev (? symbol? x) (cons φ κ))
       (execute/trace `(lookup-var ',x)
                      `(pop-continuation))
       (ko φ κ))
      ((ev `(begin ,es ...) κ)
       (eval-seq es κ))
      ((ev `(can-close-loop ,e) κ)
       (execute/trace `(push-continuation ,(can-close-loopk)))
       (ev e (cons (can-close-loopk) κ)))
      ((ev `(can-start-loop ,e ,debug-info) κ)
       (execute/trace `(push-continuation ,(can-start-loopk e '())))
       (ev debug-info (cons (can-start-loopk e '()) κ)))
      ((ev `(cond) (cons φ κ))
       (execute/trace `(literal-value ())
                      `(pop-continuation))
       (ko φ κ))      
      ((ev `(cond (else . ,es)) κ)
       (eval-seq es κ))
      ((ev `(cond (,pred . ,pes) . ,es) κ)
       (execute/trace `(save-env)
                      `(push-continuation ,(condk pes es)))
       (ev pred (cons (condk pes es) κ)))
      ((ev `(define ,pattern . ,expressions) κ)
       (if (symbol? pattern)
           (begin (execute/trace `(save-env)
                                 `(push-continuation ,(definevk pattern)))
                  (ev (car expressions) (cons (definevk pattern) κ)))
           (begin (execute/trace `(alloc-var ',(car pattern))
                                 `(create-closure ',(cdr pattern) ',expressions)
                                 `(set-var ',(car pattern))
                                 `(pop-continuation))
                  (match κ
                    ((cons φ κ) (ko φ κ))))))
      ((ev `(if ,e ,e1 . ,e2) κ)
       (execute/trace `(save-env)
                      `(push-continuation ,(ifk e1 e2)))
       (ev e (cons (ifk e1 e2) κ)))
      ((ev `(is-evaluating ,e) κ)
       (execute/trace `(push-continuation ,(is-evaluatingk)))
       (ev e (cons (is-evaluatingk) κ)))
      ((ev `(lambda ,x ,es ...) (cons φ κ))
       (execute/trace `(create-closure ',x ',es)
                      `(pop-continuation))
       (ko φ κ))
      ((ev `(let () . ,expressions)  κ)
       (eval-seq expressions κ))
      ((ev `(let ((,var ,val) . ,bds) . ,es) κ)
       (unless (null? bds)
         (error "Syntax error: let used with more than one binding: " bds))
       (execute/trace `(save-env)
                      `(push-continuation ,(letk var es)))
       (ev val (cons (letk var es) κ)))
      ((ev `(let* () . ,expressions) κ)
       (eval-seq expressions κ))
      ((ev `(let* ((,var ,val) . ,bds) . ,es) κ)
       (execute/trace `(save-env)
                      `(push-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ev `(letrec ((,x ,e) . ,bds) . ,es) κ)
       (execute/trace `(literal-value '())
                      `(alloc-var ',x)
                      `(save-env)
                      `(push-continuation ,(letreck x bds es)))
       (ev e (cons (letreck x bds es) κ)))
      ((ev `(or ,e . ,es) κ)
       (execute/trace `(push-continuation ,(ork es)))
       (ev e (cons (ork es) κ)))
      ((ev `(quote ,e) (cons φ κ))
       (execute/trace `(quote-value ',e)
                      `(pop-continuation))
       (ko φ κ))
      ((ev `(set! ,x ,e) κ)
       (execute/trace `(save-env)
                      `(push-continuation  ,(setk x)))
       (ev e (cons (setk x) κ)))
      ((ev `(,rator) κ)
       (execute/trace `(save-env)
                      `(push-continuation ,(ratork 0 'regular-nulary)))
       (ev rator (cons (ratork 0 'regular-nulary) κ)))
      ((ev `(,rator . ,rands) κ)
       (execute/trace `(save-env))
       (let ((rrands (reverse rands)))
         (execute/trace `(push-continuation ,(randk rator (cdr rrands) 1)))
         (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
      ((ev e (cons φ κ))
       (execute/trace `(literal-value ,e)
                      `(pop-continuation))
       (ko φ κ))
      ((ko (andk '()) κ)
       (execute/trace `(pop-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (andk '()) (cons φ κ))
       (execute/trace `(pop-continuation))
       (ko φ κ))
      ((ko (andk es) κ)
       (if v
           (begin (execute/trace `(push-continuation  ,(andk (cdr es))))
                  (ev (car es) (cons (andk (cdr es)) κ)))
           (begin (execute/trace `(pop-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (applicationk debug) κ)
       (execute/trace `(restore-env)
                      `(pop-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (apply-failedk rator i) κ)
       (execute/trace `(save-all-vals)
                      `(save-env)
                      `(push-continuation ,(ratork i 'apply)))
       (ev rator (cons (ratork i 'apply) κ)))
      ((ko (applyk rator) κ)
       (let ((i (length v)))
         (execute/trace `(guard-same-nr-of-args ,i ',rator ,(inc-guard-id!))
                        `(save-all-vals)
                        `(save-env)
                        `(push-continuation ,(ratork i 'apply)))
         (ev rator (cons (ratork i 'apply) κ))))
      ((ko (closure-guard-failedk i) κ)
       (do-function-call i κ))
      ((ko (condk pes '()) κ)
       (execute/trace `(restore-env))
       (if v
           (begin (execute/trace `(guard-true ,(inc-guard-id!) '()))
                  (eval-seq pes κ))
           (begin (execute/trace `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                                 `(literal-value '())
                                 `(pop-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (condk pes `((else . ,else-es))) κ)
       (execute/trace `(restore-env))
       (if v
           (begin (execute/trace `(guard-true ,(inc-guard-id!) ',`(begin ,@else-es)))
                  (eval-seq pes κ))
           (begin (execute/trace `(guard-false ,(inc-guard-id!) ',`(begin ,@pes)))
                  (eval-seq else-es κ))))
      ((ko (condk pes `((,pred . ,pred-es) . ,es)) κ)
       (execute/trace `(restore-env))
       (if v
           (begin (execute/trace `(guard-true ,(inc-guard-id!) ',`(cond ,@es)))
                  (eval-seq pes κ))
           (begin (execute/trace `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                                 `(save-env)
                                 `(push-continuation ,(condk pred-es es)))
                  (ev pred (cons (condk pred-es es) κ)))))
      ((ko (definevk x) (cons φ κ))
       (execute/trace `(restore-env)
                      `(alloc-var ',x)
                      `(pop-continuation))
       (ko φ κ))
      ((ko (haltk) _)
       #f) 
      ((ko (ifk e1 e2) κ)
       (execute/trace `(restore-env))
       (let ((new-guard-id (inc-guard-id!)))
         (if v
             (begin (execute/trace `(guard-true ,new-guard-id ',(if (null? e2)
                                                                    '()
                                                                    ;; If the guard fails, the predicate was false, so e2 should be evaluated
                                                                    (car e2)))) 
                    (ev e1 κ))
             ;; If the guard fails, the predicate was true, so e1 should be evaluated
             (begin (execute/trace `(guard-false ,new-guard-id ',e1)) 
                    (if (null? e2)
                        (begin (execute/trace `(pop-continuation)
                                              `(literal-value '()))
                               (ko (car κ) (cdr κ)))
                        (ev (car e2) κ))))))
      ((ko (letk x es) κ)
       (execute/trace `(restore-env)
                      `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x '() es) κ)
       (execute/trace `(restore-env)
                      `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x `((,var ,val) . ,bds) es) κ)
       (execute/trace `(restore-env)
                      `(alloc-var ',x)
                      `(save-env)
                      `(push-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ko (letreck x '() es) κ)
       (execute/trace `(restore-env)
                      `(set-var ',x))
       (eval-seq es κ))
      ((ko (letreck x `((,var ,val) . ,bds) es) κ)
       (execute/trace `(restore-env)
                      `(set-var ',x)
                      `(alloc-var ',var)
                      `(save-env)
                      `(push-continuation ,(letreck var bds es)))
       (ev val (cons (letreck var bds es) κ)))
      ((ko (ork '()) κ)
       (execute/trace `(pop-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (ork es) κ)
       (if v
           (begin (execute/trace `(pop-continuation))
                  (ko (car κ) (cdr κ)))
           (ev `(or ,@es) κ)))
      ((ko (randk rator '() i) κ)
       (execute/trace `(restore-env)
                      `(save-val)
                      `(save-env)
                      `(push-continuation ,(ratork i 'regular)))
       (ev rator (cons (ratork i 'regular) κ)))
      ((ko (randk rator rands i) κ)
       (execute/trace `(restore-env)
                      `(save-val)
                      `(save-env)
                      `(push-continuation ,(randk rator (cdr rands) (+ i 1))))
       (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
      ((ko (ratork i debug) κ)
       (execute/trace `(restore-env)
                      `(guard-same-closure ,v ,i  ,(inc-guard-id!)))
       (do-function-call i κ))
      ((ko (seqk '()) (cons φ κ)) ; No tailcall optimization!
       (execute/trace `(restore-env)
                      `(pop-continuation))
       (ko φ κ))
      ((ko (seqk (cons e exps)) κ)
       (execute/trace `(push-continuation ,(seqk exps)))
       (ev e (cons (seqk exps) κ)))
      ((ko (setk x) (cons φ κ))
       (execute/trace `(restore-env)
                      `(set-var ',x)
                      `(pop-continuation))
       (ko φ κ))))
  
  (define (step* tracer-context s)
    (match s
      ((ko (haltk) _)
       v)
      ;; Evaluate annotations in step* instead of step
      ;; Annotations might not lead to recursive call to step*
      ((ko (is-evaluatingk) (cons φ κ))
       (handle-is-evaluating-annotation-reg (ko φ κ)))
      ((ev `(splits-control-flow) (cons φ κ))
       (handle-splits-cf-annotation-reg tracer-context (ko φ κ)))
      ((ev `(merges-control-flow) (cons φ κ))
       (handle-merges-cf-annotation-reg (ko φ κ)))
      ((ko (can-close-loopk) (cons φ κ))
       (handle-can-close-loop-annotation-reg v (ko φ κ)))
      ((ko (can-start-loopk label '()) κ)
       (execute/trace tracer-context `(push-continuation ,(can-start-loopk '() v)))
       (run-evaluator tracer-context (ev label (cons (can-start-loopk '() v) κ))))
      ((ko (can-start-loopk '() debug-info) (cons φ κ))
       (handle-can-start-loop-annotation-reg v debug-info (ko φ κ)))
      (_
       (let ((new-state (step tracer-context s)))
         (run-evaluator tracer-context new-state)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                     Running tracing interpreter                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (do-is-executing-trace-state tracer-context program-state)
    (define (guard-failed sentinel guard-id state)
      ;; Stop tracing whatever is being traced and start tracing the guard associated with this
      ;; guard-id.
      (define (switch-to-trace-guard! guard-id old-trace-key)
        (stop-tracing-abnormal!)
        (start-tracing-guard! guard-id old-trace-key))
      (output "------ BOOTSTRAP: GUARD-ID: ") (output guard-id) (output " ------") (output-newline)
      (cond ((guard-trace-exists? guard-id)
             (output "----------- STARTING FROM GUARD ") (output guard-id) (output " -----------") (output-newline)
             (execute-guard-trace guard-id))
            ((not (is-tracing?))
             (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
             (let ((trace-key-executing (get-label-trace-executing-trace-key)))
               ;; Trace-nodes executing stack will be flushed
               (start-tracing-guard! guard-id trace-key-executing)
               (bootstrap-to-evaluator state)))
            (else
             ;; Interpreter is tracing, has traced a jump to an existing (inner) trace and in this
             ;; inner trace a guard-failure has now occurred. Abandon the existing trace and start
             ;; tracing from this new guard-failure.
             (output "----------- ABANDONING CURRENT TRACE; SWITCHING TO TRACE GUARD: ") (output guard-id) (output-newline)
             (let ((trace-key-executing (get-label-trace-executing-trace-key)))
               (switch-to-trace-guard! guard-id trace-key-executing)
               (bootstrap-to-evaluator state)))))
    (define (do-trace-execution)
      )
    (let ((answer (call/cc (lambda (k) (set-global-continuation! k)
                             (list 'normal)))))
      (if (eq? (car answer) 'normal)
          (do-trace-execution)
          (apply guard-failed (cdr answer)))))
    
  
  (define (do-is-tracing-state tracer-context program-state)
    (match program-state
      ((ko (haltk) _)
       v)
      ;; Evaluate annotations in step* instead of step
      ;; Annotations might not lead to recursive call to step*
      ((ko (is-evaluatingk) (cons φ κ))
       (handle-is-evaluating-annotation-reg tracer-context (ko φ κ)))
      ((ev `(splits-control-flow) (cons φ κ))
       (handle-splits-cf-annotation-reg tracer-context (ko φ κ)))
      ((ev `(merges-control-flow) (cons φ κ))
       (handle-merges-cf-annotation-tracing tracer-context (ko φ κ)))
      ((ko (can-close-loopk) (cons φ κ))
       (handle-can-close-loop-annotation-tracing tracer-context v (ko φ κ)))
      ((ko (can-start-loopk label '()) κ)
       (execute/trace tracer-context `(push-continuation ,(can-start-loopk '() v)))
       (run-evaluator tracer-context (ev label (cons (can-start-loopk '() v) κ))))
      ((ko (can-start-loopk '() debug-info) (cons φ κ))
       (handle-can-start-loop-annotation-tracing tracer-context v debug-info (ko φ κ)))
      (_
       (let ((new-state (step tracer-context s)))
         (run-evaluator tracer-context new-state)))))
  
  (define (run-evaluator tracer-context program-state)
    (cond ((is-executing-trace? tracer-context)
           (do-is-executing-trace-state tracer-context program-state))
          ((is-regular-interpreting? tracer-context)
           (step* tracer-context program-state))
          ((is-tracing? program-state)
           (do-is-tracing-state tracer-context program-state))
          (else
           (error "Unknown tracer-context-state: " (tracer-context-state tracer-context)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                           Guard failure                                              ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (guard-failed-with-ev guard-id e)
    (guard-failed guard-id (ev e τ-κ)))
  
  (define (guard-failed-with-ko guard-id φ)
    (guard-failed guard-id (ko φ τ-κ)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Starting evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Resetting evaluator
  ;
  
  ;;; Resets all bookkeeping behind the tracing interpreter.
  (define (reset! tracer-context)
    (set! ρ (make-new-env))
    (set! σ (new-store))
    (set! θ '())
    (set! τ-κ `(,(haltk)))
    (clear-trace! tracer-context)
    (reset-metrics!)
    (reset-random-generator!)
    (reset-trace-outputting!))
  
  ;
  ; Starting evaluator
  ;
  
  ;;; Transforms the given expression into a CK state, so that it can be used by the evaluator.
  (define (inject e)
    (ev e `(,(haltk))))
  
  (define (run s)
    (let ((tracer-context (new-tracer-context)))
      (reset! tracer-context)
      (apply run-evaluator
             (let ((combined-state (call/cc (lambda (k)
                                              (set-global-continuation! k)
                                              (list tracer-context s)))))
               (flush-label-traces-executing! tracer-context)
               combined-state))))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read)))))