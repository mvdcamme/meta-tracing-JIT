(module evaluator racket
  
  (require (rename-in "cesk-interpreter.scm"
                      (step cesk-step))
           "continuations.scm"
           "environment.scm"
           "interaction.scm"
           "instruction-set.scm"
           "output.scm"
           "predefined-functions.scm"
           "tracing.scm")
  
  (provide inject
           run)
  
  ;
  ; Constants
  ;
  
  (define TRACING_THRESHOLD 5)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                           Evaluator state                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (struct evaluator-state (state
                           tracer-context
                           program-state
                           trace-executing) #:transparent)
  
  (define-syntax evaluator-state-copy
    (syntax-rules ()
      ((_ an-evaluator-state ...)
       (struct-copy evaluator-state an-evaluator-state ...))))
  
  ;
  ; States
  ;
  
  (define EXECUTING_STATE 'executing-trace)
  (define INTERPRETING_STATE 'regular-interpretation)
  (define TRACING_STATE 'tracing)
  
  (define (state-equals? evaluator-state state)
    (eq? (evaluator-state-state evaluator-state) state))
  
  (define (is-executing? evaluator-state)
    (state-equals? evaluator-state EXECUTING_STATE))
  
  (define (set-executing-trace-state evaluator-state)
    (set-state evaluator-state EXECUTING_STATE))
  
  (define (is-interpreting? evaluator-state)
    (state-equals? evaluator-state INTERPRETING_STATE))
  
  (define (set-interpreting-state evaluator-state)
    (set-state evaluator-state INTERPRETING_STATE))
  
  (define (is-tracing? evaluator-state)
    (state-equals? evaluator-state TRACING_STATE))
  
  (define (set-tracing-state evaluator-state)
    (set-state evaluator-state TRACING_STATE))
  
  (define (set-state evaluator-state new-state)
    (evaluator-state-copy evaluator-state (state new-state)))
  
  ;
  ; Constructors
  ;
  
  (define (make-executing-state tracer-context program-state trace-node)
    (evaluator-state EXECUTING_STATE tracer-context program-state trace-node))
  
  (define (make-interpreting-state tracer-context program-state)
    (evaluator-state INTERPRETING_STATE tracer-context program-state #f))
  
  (define (make-tracing-state tracer-context program-state)
    (evaluator-state TRACING_STATE tracer-context program-state #f))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                          Running evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define prev-state 'interpreting)
  (define curr-state #f)
  
  (struct evaluation-done (value) #:transparent)
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-regular label new-program-state tracer-context)
    (outputln "reg closing annotation: tracing loop " 'd) (outputln label 'd) (output-newline 'd)
    (make-interpreting-state tracer-context new-program-state))
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-tracing label new-program-state trace tracer-context)
    (outputln "tracing closing annotation: tracing loop " 'd) (outputln label 'd)
    (if (is-tracing-label? tracer-context label)
        (make-interpreting-state (stop-tracing tracer-context #f) new-program-state)
        (make-tracing-state (append-trace tracer-context trace) new-program-state)))
  
  (define (step-merges-cf-encountered-tracing new-program-state trace tracer-context)
    (outputln "tracing: merges-cf annotation" 'd)
    (let* ((current-trace-key (tracer-context-trace-key tracer-context))
           (label (trace-key-label current-trace-key))
           (debug-info (trace-key-debug-info current-trace-key))
           (mp-id (top-splits-cf-tc tracer-context))
           (mp-trace-key (make-mp-trace-key label debug-info mp-id))
           (appended-tracer-context (append-trace tracer-context (append trace (list (pop-splits-cf)))))
           (stopped-tracer-context (stop-tracing appended-tracer-context #f))
           (popped-tracer-context (pop-splits-cf-tc stopped-tracer-context)))
      (if (trace-exists? popped-tracer-context mp-trace-key)
          (let ((mp-trace-node (get-trace popped-tracer-context mp-trace-key)))
            (outputln "mp-trace-node found" 'e)
            (make-executing-state popped-tracer-context new-program-state mp-trace-node))
          (begin (outputln "mp-trace-node NOT found" 'e)
                 (make-tracing-state (start-tracing-mp popped-tracer-context label debug-info mp-id)
                              new-program-state)))))
  
  (define (step-splits-cf-encountered-tracing new-program-state trace tracer-context)
    (outputln "tracing: splits-cf annotation" 'e)
    (let ((new-mp-id (inc-splits-cf-id!)))
      (make-tracing-state (push-splits-cf-tc (append-trace tracer-context (append trace (list (push-splits-cf new-mp-id))))
                                             new-mp-id)
                          new-program-state)))
  
  (define (step-can-start-loop-encountered-regular label debug-info new-program-state trace tracer-context)
    (let ((trace-key (make-label-trace-key label debug-info)))
      (define (can-start-tracing?)
        (>= (get-times-label-encountered tracer-context label) TRACING_THRESHOLD))
      (cond ((trace-exists? tracer-context trace-key)
             (outputln label 'd)
             (outputln "reg ----------- EXECUTING TRACE -----------" 'd)
             (make-executing-state tracer-context new-program-state (get-trace tracer-context trace-key)))
            ;; We have determined that it is worthwile to trace this label/loop, so start tracing.
            ((can-start-tracing?)
             (outputln label 'd)
             (outputln "reg ----------- STARTED TRACING -----------" 'd)
             (make-tracing-state (start-tracing-label tracer-context label debug-info) new-program-state))
            ;; Loop is not hot yet, increase hotness counter and continue interpreting
            (else
             (make-interpreting-state (inc-times-label-encountered tracer-context label) new-program-state)))))
  
  (define (step-can-start-loop-encountered-tracing label debug-info new-program-state trace tracer-context)
    (let ((trace-key (make-label-trace-key label debug-info)))
      (cond ((is-tracing-label? tracer-context label)
             (outputln label 'd)
             (outputln "tracing ----------- TRACING FINISHED; EXECUTING TRACE -----------" 'd)
             (let* ((temp-tracer-context (stop-tracing (append-trace tracer-context trace) #t)))
               (make-executing-state temp-tracer-context new-program-state (get-trace temp-tracer-context trace-key))))
            (else
             (make-tracing-state (append-trace tracer-context trace) new-program-state)))))
  
  (define (evaluate evaluator-state)
    (define (continue-with-program-state-regular new-program-state)
      (evaluator-state-copy evaluator-state
                            (program-state new-program-state)))
    (define (continue-with-program-state-tracing new-program-state new-trace)
      (evaluator-state-copy evaluator-state
                            (tracer-context (append-trace (evaluator-state-tracer-context evaluator-state) new-trace))
                            (program-state new-program-state)))
    (define (do-cesk-interpreter-step)
      (cesk-step (evaluator-state-program-state evaluator-state)))
    (define (do-trace-executing-step)
      (let* ((trace-node (evaluator-state-trace-executing evaluator-state))
             (trace (trace-node-trace trace-node))
             (label (trace-key-label (trace-node-trace-key trace-node))))
        (if (null? trace)
            (let* ((program-state (evaluator-state-program-state evaluator-state))
                   (κ (program-state-κ program-state))
                   (new-c (ko (car κ)))
                   (new-κ (cdr κ))
                   (new-program-state (program-state-copy program-state
                                                          (c new-c)
                                                          (κ new-κ))))
              (set-interpreting-state (evaluator-state-copy evaluator-state
                                                            (program-state new-program-state)
                                                            (trace-executing #f))))
            (let* ((instruction (car trace))
                   (program-state
                    (evaluator-state-program-state evaluator-state)))
              (handle-response-executing (instruction program-state))))))
    (define (handle-response-executing response)
      (let* ((tracer-context (evaluator-state-tracer-context evaluator-state))
             (trace-executing (evaluator-state-trace-executing evaluator-state))
             (trace-key (trace-node-trace-key trace-executing))
             (trace (trace-node-trace trace-executing))
             (old-program-state (evaluator-state-program-state evaluator-state)))
        (define (do-guard-failure guard-id new-c)
          (if (trace-exists? tracer-context (make-guard-trace-key (trace-key-label trace-key) (trace-key-debug-info trace-key) guard-id))
              ;; A guard trace already exists, start executing it
              (let* ((guard-trace (get-trace tracer-context (make-guard-trace-key (trace-key-label trace-key)
                                                                                    (trace-key-debug-info trace-key)
                                                                                    guard-id))))
                (make-executing-state tracer-context old-program-state guard-trace))
              ;; A guard trace does not exist yet, start tracing it
              (let* ((trace-node-executing-trace-key (trace-node-trace-key trace-executing))
                     (label (trace-key-label trace-node-executing-trace-key))
                     (debug-info (trace-key-debug-info trace-node-executing-trace-key))
                     (κ (program-state-κ old-program-state))
                     (new-program-state (program-state-copy old-program-state
                                                            (c new-c)
                                                            (κ κ))))
                (make-tracing-state (start-tracing-guard tracer-context label debug-info guard-id) new-program-state))))
        (match response
          ((normal-return new-program-state)
           (evaluator-state-copy evaluator-state
                                 (program-state new-program-state)
                                 (trace-executing (trace-node-copy (evaluator-state-trace-executing evaluator-state)
                                                                   (trace (cdr trace))))))
          ((error-return (do-push-splits-cf mp-id))
           (let* ((trace-node-executing (evaluator-state-trace-executing evaluator-state))
                  (trace-executing (trace-node-trace trace-node-executing))
                  (new-trace-node-executing (trace-node-copy trace-node-executing
                                                             (trace (cdr trace-executing)))))
             (evaluator-state-copy evaluator-state
                                   (tracer-context (push-splits-cf-tc tracer-context mp-id))
                                   (trace-executing new-trace-node-executing))))
          ((error-return (do-pop-splits-cf))
           (let* ((mp-id (top-splits-cf-tc tracer-context))
                  (current-trace-key-executing (trace-node-trace-key (evaluator-state-trace-executing evaluator-state)))
                  (label (trace-key-label current-trace-key-executing))
                  (debug-info (trace-key-debug-info current-trace-key-executing))
                  (mp-trace-key (make-mp-trace-key label debug-info mp-id))
                  (mp-trace-node (get-trace tracer-context mp-trace-key))
                  (popped-tracer-context (pop-splits-cf-tc tracer-context)))
             (outputln "Executing mp trace" 'e)
             (evaluator-state-copy evaluator-state
                                   (tracer-context popped-tracer-context)
                                   (trace-executing mp-trace-node))))
          ((error-return (guard-failed guard-id c))
           (do-guard-failure guard-id c))
          ((error-return (trace-loops))
           (let* ((old-trace-node (evaluator-state-trace-executing evaluator-state))
                  (old-trace-key (trace-node-trace-key old-trace-node))
                             ;; We are definitely looking for a label-trace here, so make a label-trace-key
                  (trace-key (make-label-trace-key (trace-key-label old-trace-key)
                                                   (trace-key-debug-info old-trace-key))) 
                  (new-trace-node (get-trace tracer-context trace-key)))
             (evaluator-state-copy evaluator-state
                                   (trace-executing new-trace-node)))))))
    (define (handle-annotation-signal-regular new-program-state trace annotation-signal)
      (let ((tracer-context (evaluator-state-tracer-context evaluator-state)))
        (match annotation-signal
          ((is-evaluating-encountered _)
           ;; TODO Just ignore for the moment
           (continue-with-program-state-regular new-program-state))
          ((can-start-loop-encountered label debug-info)
           (step-can-start-loop-encountered-regular label debug-info new-program-state trace tracer-context))
          ((can-close-loop-encountered label)
           (step-can-close-loop-encountered-regular label new-program-state tracer-context))
          ((merges-cf-encountered)
           (make-interpreting-state (pop-splits-cf-tc tracer-context) new-program-state))
          ((splits-cf-encountered)
           (make-interpreting-state (push-splits-cf-tc tracer-context (inc-splits-cf-id!)) new-program-state)))))
    (define (handle-annotation-signal-tracing new-program-state trace annotation-signal)
      (let ((tracer-context (evaluator-state-tracer-context evaluator-state)))
        (match annotation-signal
          ((is-evaluating-encountered _)
           ;; TODO Just ignore for the moment
           (continue-with-program-state-tracing new-program-state trace))
          ((can-start-loop-encountered label debug-info)
           (step-can-start-loop-encountered-tracing label debug-info new-program-state trace tracer-context))
          ((can-close-loop-encountered label)
           (step-can-close-loop-encountered-tracing label new-program-state trace tracer-context))
          ((merges-cf-encountered)
           (step-merges-cf-encountered-tracing new-program-state trace tracer-context))
          ((splits-cf-encountered)
           (step-splits-cf-encountered-tracing new-program-state trace tracer-context)))))
    (define (handle-response-abnormal response)
      (match response
        ((cesk-abnormal-return (cesk-stopped))
         (evaluation-done (program-state-v (evaluator-state-program-state evaluator-state))))
        ((cesk-abnormal-return signal)
         (error "Abnormal return value from cesk interpreter" signal))))
    (define (handle-response-regular response)
      (match response
        ((cesk-normal-return new-program-state _ #f)
         (continue-with-program-state-regular new-program-state))
        ((cesk-normal-return new-program-state trace annotation-signal)
         (handle-annotation-signal-regular new-program-state trace annotation-signal))
        (_
         (handle-response-abnormal response))))
    (define (handle-response-tracing response)
      (match response
        ((cesk-normal-return new-program-state trace #f)
         (continue-with-program-state-tracing new-program-state trace))
        ((cesk-normal-return new-program-state trace annotation-signal)
         (handle-annotation-signal-tracing new-program-state trace annotation-signal))
        (_
         (handle-response-abnormal response))))
    (define (step)
      (match evaluator-state
        ((? is-executing?) ;(outputln "executing" 'v)
                           (do-trace-executing-step))
        ((? is-interpreting?) ;(outputln "interpreting" 'd)
                              (handle-response-regular (do-cesk-interpreter-step)))
        ((? is-tracing?) ;(outputln "tracing" 'd)
                         (handle-response-tracing (do-cesk-interpreter-step)))
        (_ (error "Unknown state" (evaluator-state-state evaluator-state)))))
    (if (evaluation-done? evaluator-state)
        (evaluation-done-value evaluator-state)
        (evaluate (step))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Starting evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Creates a new store that contains all predefined functions/variables.
  (define (make-new-store)
    '())
  
  ;;; Transforms the given expression into a CK state, so that it can be used by the evaluator.
  (define (inject-c e)
    (ev e))
  
  (define (inject-program-state e)
    (program-state (inject-c e)
                   (add-functions-to-environment (make-new-env))
                   (add-functions-to-store (make-new-store))
                   '()
                   #f
                   `(,(haltk))))
  
  (define (inject e)
    (make-interpreting-state (new-tracer-context) (inject-program-state e)))
  
  (define (run evaluator-state)
    (evaluate evaluator-state))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read)))))