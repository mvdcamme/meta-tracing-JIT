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
           GLOBAL_TRACER_CONTEXT
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
  
  ;;; The amount of times a label needs to be encountered before it is considered 'hot'.
  (define TRACING_THRESHOLD 5)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                             CK machine                                               ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Registers
  ;
  
  ;;; Stores the continuation stack during program execution.
  ;;; This stack is needed to switch back from trace execution to regular program interpretation.
  (define τ-κ #f) ;continuation stack
  
  ;;; Creates a new store that contains all predefined functions/variables.
  (define (new-store)
    (let ((dict (new-dictionary = 100 (lambda (splits-cf-id) splits-cf-id))))
      (insert! dict meta-random-address meta-random)
      (insert! dict pseudo-random-generator-address PSEUDO_RANDOM_GENERATOR)
      dict))
  
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
                         (bootstrap-to-evaluator state))))))
  
  ;;; Executes the trace of the given label-trace-node.
  (define (execute-label-trace-with-trace-node label-trace-node)
    (let ((trace (trace-node-trace label-trace-node)))
      ;; Benchmarking: record the fact that this trace node will be executed
      (add-execution! label-trace-node)
      (execute/trace `(let ()
                        ;; Push this trace-node on the stack of label-traces being executed
                        (push-label-trace-executing! ,label-trace-node)
                        (let ((state (execute-trace ',trace))) ; Actually execute the trace
                          ;; Pop this trace-node again
                          (pop-label-trace-executing!)
                          ;; Return the CK state
                          state)))))
  
  ;;; Execute the label-trace associated with the given id.
  (define (execute-label-trace-with-id label-trace-id)
    (let ((label-trace-node (find (tracer-context-trace-nodes-dictionary GLOBAL_TRACER_CONTEXT) label-trace-id)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  ;;; Execute the label-trace associated with the given label.
  (define (execute-label-trace-with-label label)
    (let ((label-trace-node (get-label-trace label)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  ;;; Execute the merge-point-tail-trace associated with the given merge-point-id.
  (define (execute-mp-tail-trace mp-id state)
    (let* ((mp-tails-dictionary (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
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
                 (push-label-trace-executing-if-not-on-top! label-trace-node)
                 (let ((state (execute-trace (trace-node-trace mp-tail-trace))))
                   ;; Pop this trace-node again
                   (pop-label-trace-executing!)
                   (bootstrap-to-evaluator state)))
          (bootstrap-to-evaluator state))))
  
  ;;; Executes the given instructions by calling the Racket native 'eval' function on them and
  ;;; returns the last value that was evaluated.
  (define (eval-instructions ms)
    (for/last ((instruction ms))
      (eval instruction)))
  
  ;;; Executes the given instructions and records them into the trace, if the interpreter is
  ;;; currently tracing.
  (define (execute/trace . ms)
    (when (is-tracing?)
      (append-trace! ms))
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
  (define (handle-is-evaluating-annotation state)
    (execute/trace `(pop-continuation))
    (set-root-expression-if-uninitialised! v)
    (when (is-tracing?)
      (add-ast-node-traced! v))
    (step* state))
  
  ;
  ; Starting/ending trace recording
  ;
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (handle-can-close-loop-annotation label state)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (when (is-tracing-label? label)
      (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
      (stop-tracing! #f))
    (execute/trace `(pop-continuation))
    (step* state))
  
  (define (check-stop-tracing-label label state)
    (define (do-stop-tracing!)
      (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
      (stop-tracing! #t)
      (let ((new-state (execute-label-trace-with-label label)))
        (step* new-state)))
    (define (do-continue-tracing)
      (output "----------- CONTINUING TRACING -----------") (output-newline)
      (execute/trace `(pop-continuation))
      (step* state))
    (inc-times-label-encountered-while-tracing!)
    (if (times-label-encountered-greater-than-threshold?)
        (do-stop-tracing!)
        (do-continue-tracing)))
  
  ;;; Handles the (can-start-loop label debug-info) annotation. If it is decided not to
  ;;; start executing the trace belonging to this label, regular interpretation continues
  ;;; with the given state.
  (define (handle-can-start-loop-annotation label debug-info state)
    ;; Continue regular interpretation with the given state.
    (define (continue-with-state)
      (execute/trace `(pop-continuation))
      (step* state))
    ;; Check whether it is worthwile to start tracing this label.
    ;; In this implementation, whether it is worthwile to trace a label only depends
    ;; on how hot the corresponding loop is: how many times has this label been encountered yet?
    (define (can-start-tracing-label?)
      (>= (get-times-label-encountered label) TRACING_THRESHOLD))
          ;; We are currently tracing this label: check if this label refers to a 'true' loop.
    (cond ((is-tracing-label? label)
           (check-stop-tracing-label label state))
          ;; A trace for this label already exists, so start executing that trace?
          ((label-trace-exists? label)
           (output "----------- EXECUTING TRACE -----------") (output-newline)
           (let ((label-trace (get-label-trace label)))
             ;; If we are already tracing, and this trace is a 'true' loop, we record
             ;; a jump to this already existing trace.
             ;; Else, we ignore the existing trace and just inline everything.
             (if (or (not (is-tracing?)) (label-trace-loops? label-trace))
                 (let ((new-state (execute-label-trace-with-label label)))
                   (step* new-state))
                 (continue-with-state))))
          ;; We are not tracing anything at the moment, and we have determined that it
          ;; is worthwile to trace this label/loop, so start tracing.
          ((and (not (is-tracing?)) (can-start-tracing-label?))
           (output "----------- STARTED TRACING -----------") (output-newline)
           (start-tracing-label! label debug-info)
           (continue-with-state))
          ;; We are already tracing and/or it is not worthwile to trace this label,
          ;; so continue regular interpretation. We do increase the counter for the number
          ;; of times this label has been encountered (i.e., we raise the 'hotness' of this loop).
          (else
           (inc-times-label-encountered! label)
           (when (is-tracing?)
             (output "----------- ALREADY TRACING ANOTHER LABEL -----------") (output-newline))
           (continue-with-state))))
  
  ;
  ; Trace merging
  ;
  
  ;;; Handles the (merges-control-flow) annotation.
  (define (handle-merges-cf-annotation continuation)
    (output "MERGES CONTROL FLOW") (output-newline)
    (let ((mp-id (top-splits-cf-id)))
      (execute/trace `(pop-continuation)
                     `(pop-splits-cf-id!))
      (if (is-tracing?)
          (begin
            (append-trace! `((execute-mp-tail-trace ,mp-id ,continuation)))
            ((tracer-context-merges-cf-function GLOBAL_TRACER_CONTEXT) (reverse τ))
            (if (mp-tail-trace-exists? mp-id)
                (begin (output "MP TAIL TRACE EXISTS") (output-newline)
                       (stop-tracing-normal!)
                       (let ((new-state (eval `(execute-mp-tail-trace ,mp-id ,continuation))))
                         (step* new-state)))
                (begin (output "MP TAIL TRACE DOES NOT EXIST") (output-newline)
                       (start-tracing-mp-tail! mp-id)
                       (step* continuation))))
          (step* continuation))))
  
  ;;; Handles the (splits-control-flow) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (handle-splits-cf-annotation state)
    (execute/trace `(pop-continuation)
                   `(push-splits-cf-id! ,(inc-splits-cf-id!)))
    (step* state))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Running evaluator                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (bootstrap-to-evaluator state)
    (call-global-continuation state))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                           Guard failure                                              ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (guard-failed guard-id state)
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
  (define (reset!)
    (set! ρ (make-new-env))
    (set! σ (new-store))
    (set! θ '())
    (set! τ-κ `(,(haltk)))
    (reset-global-tracer-context!)
    (clear-trace!)
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
    (reset!)
    (apply step* (list (let ((v (call/cc (lambda (k)
                                           (set-global-continuation! k)
                                           s))))
                         (flush-label-traces-executing!)
                         v))))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read)))))