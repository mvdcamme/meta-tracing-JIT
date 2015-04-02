(module evaluator racket
  
  (require (rename-in "cesk-interpreter.scm"
                      (step cesk-step))
           "continuations.scm"
           "environment.scm"
           "interaction.scm"
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
  
  (struct evaluator-state-struct (state
                                  tracer-context
                                  program-state
                                  trace-executing) #:transparent)
  
  (define-syntax evaluator-state-copy
    (syntax-rules ()
      ((_ an-evaluator-state ...)
       (struct-copy evaluator-state-struct an-evaluator-state ...))))
  
  ;
  ; States
  ;
  
  (define EXECUTING_STATE 'executing-trace)
  (define INTERPRETING_STATE 'regular-interpretation)
  (define TRACING_STATE 'tracing)
  
  (define (state-equals? evaluator-state state)
    (eq? (evaluator-state-struct-state evaluator-state) state))
  
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
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                          Running evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-regular label new-program-state tracer-context)
    (output label)
    (output "reg closing annotation: tracing loop ") (output label) (output-newline)
    (evaluator-state-struct INTERPRETING_STATE
                            tracer-context
                            new-program-state
                            #f))
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-tracing label new-program-state tracer-context)
    (output label)
    (output "tracing closing annotation: tracing loop ") (output label) (output-newline)
    (if (is-tracing-label? tracer-context label)
        (evaluator-state-struct INTERPRETING_STATE
                                (stop-tracing tracer-context #f)
                                new-program-state
                                #f)
        (evaluator-state-struct TRACING_STATE
                                tracer-context
                                new-program-state
                                #f)))
  
  (struct trace-assoc (label
                       trace) #:transparent)
  
  (define-syntax trace-assoc-copy
    (syntax-rules ()
      ((_ a-trace-assoc ...)
       (struct-copy trace-assoc a-trace-assoc ...))))
  
  (define (step-can-start-loop-encountered-regular label debug-info new-program-state trace tracer-context)
    (define (can-start-tracing-label?)
      (>= (get-times-label-encountered tracer-context label) TRACING_THRESHOLD))
    ;(displayln label)
    (cond ((label-trace-exists? tracer-context label)
           (output label)
           (displayln "reg ----------- EXECUTING TRACE -----------") (output-newline)
           (evaluator-state-struct EXECUTING_STATE
                                   tracer-context
                                   new-program-state
                                   (trace-assoc label (trace-node-trace (get-label-trace tracer-context label)))))
          ((equal? label '((display (+ param 10))))
           (displayln label)
           (displayln "reg special ----------- STARTED TRACING -----------") (output-newline)
           (evaluator-state-struct TRACING_STATE
                                   (append-trace (start-tracing-label tracer-context label debug-info) trace)
                                   new-program-state
                                   #f))
          ;; We have determined that it is worthwile to trace this label/loop, so start tracing.
          ((can-start-tracing-label?)
           (displayln label)
           (displayln "reg ----------- STARTED TRACING -----------") (output-newline)
           (evaluator-state-struct TRACING_STATE
                                   (start-tracing-label tracer-context label debug-info)
                                   new-program-state
                                   #f))
          ;; Increase the counter for the number of times this label has been encountered
          ;; (i.e., we raise the 'hotness' of this loop).
          (else
           (evaluator-state-struct INTERPRETING_STATE
                                   (inc-times-label-encountered tracer-context label)
                                   new-program-state
                                   #f))))
  
  (define (step-can-start-loop-encountered-tracing label debug-info new-program-state trace tracer-context)
    (cond ((is-tracing-label? tracer-context label)
           (output label)
           (output "tracing ----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
           (let* ((temp-tracer-context (stop-tracing (append-trace tracer-context trace) #t)))
             (evaluator-state-struct EXECUTING_STATE
                                     temp-tracer-context
                                     new-program-state
                                     (trace-assoc label (trace-node-trace (get-label-trace temp-tracer-context label))))))
          ;; Increase the counter for the number of times this label has been encountered
          ;; (i.e., we raise the 'hotness' of this loop).
          (else
           (evaluator-state-struct TRACING_STATE
                                   (append-trace (inc-times-label-encountered tracer-context label) trace)
                                   new-program-state
                                   #f))))
  
  (define (evaluate evaluator-state)
    (define (continue-with-program-state-regular new-program-state)
      (evaluate (evaluator-state-copy evaluator-state
                                      (program-state new-program-state))))
    (define (continue-with-program-state-tracing new-program-state new-trace)
      (evaluate (evaluator-state-copy evaluator-state
                                      (tracer-context (append-trace (evaluator-state-struct-tracer-context evaluator-state) new-trace))
                                      (program-state new-program-state))))
    (define (do-cesk-interpreter-step)
      (cesk-step (evaluator-state-struct-program-state evaluator-state)))
    (define (do-trace-executing-step)
      (let* ((trace-assoc (evaluator-state-struct-trace-executing evaluator-state))
             (trace (trace-assoc-trace trace-assoc))
             (label (trace-assoc-label trace-assoc)))
        (if (null? trace)
            (begin ;(displayln "TRACE FINISHED")
                   ;(displayln (take (program-state-κ (evaluator-state-struct-program-state evaluator-state)) 10))
                   (let* ((program-state (evaluator-state-struct-program-state evaluator-state))
                          (κ (program-state-κ program-state))
                          (new-c (ko (car κ)))
                          (new-κ (cdr κ))
                          (new-program-state (program-state-copy program-state
                                                                 (c new-c)
                                                                 (κ new-κ))))
                     (set-interpreting-state (evaluator-state-copy evaluator-state
                                                                   (program-state new-program-state)
                                                                   (trace-executing #f)))))
            (let* ((instruction (car trace))
                   (program-state
                    (evaluator-state-struct-program-state evaluator-state)))
              (handle-response-executing (instruction program-state))))))
    (define (handle-response-executing response)
      (let* ((tracer-context (evaluator-state-struct-tracer-context evaluator-state))
             (trace-executing (evaluator-state-struct-trace-executing evaluator-state))
             (trace (trace-assoc-trace trace-executing))
             (old-program-state (evaluator-state-struct-program-state evaluator-state)))
        (define (guard-failed new-c)
          (let* ((κ (program-state-κ old-program-state))
                 (new-program-state (program-state-copy old-program-state
                                                        (c new-c)
                                                        (κ κ))))
            (evaluator-state-struct INTERPRETING_STATE
                                    tracer-context
                                    new-program-state
                                    #f)))
        (match response
          ((normal-return new-program-state)
           (evaluator-state-copy evaluator-state
                                 (program-state new-program-state)
                                 (trace-executing (trace-assoc-copy (evaluator-state-struct-trace-executing evaluator-state)
                                                                    (trace (cdr trace))))))
          ((error-return (guard-failed-with-ev guard-id e))
           (guard-failed (ev e)))
          ((error-return (guard-failed-with-ko guard-id φ))
           (guard-failed (ko φ)))
          ((error-return (trace-loops))
           (let* ((old-trace-assoc (evaluator-state-struct-trace-executing evaluator-state))
                  (label (trace-assoc-label old-trace-assoc))
                  (full-trace-executing (trace-node-trace (get-label-trace tracer-context label)))
                  (full-trace-executing-assoc (trace-assoc label full-trace-executing)))
             (evaluator-state-copy evaluator-state
                                   (trace-executing full-trace-executing-assoc)))))))
    (define (handle-annotation-signal-regular new-program-state trace annotation-signal)
      (let ((tracer-context (evaluator-state-struct-tracer-context evaluator-state)))
        (match annotation-signal
          ((is-evaluating-encountered _)
           ;; TODO Just ignore for the moment
           (continue-with-program-state-regular new-program-state))
          ((can-start-loop-encountered label debug-info)
           (evaluate (step-can-start-loop-encountered-regular label debug-info new-program-state trace tracer-context)))
          ((can-close-loop-encountered label)
           (evaluate (step-can-close-loop-encountered-regular label new-program-state tracer-context))))))
    (define (handle-annotation-signal-tracing new-program-state trace annotation-signal)
      (let ((tracer-context (evaluator-state-struct-tracer-context evaluator-state)))
        (match annotation-signal
          ((is-evaluating-encountered _)
           ;; TODO Just ignore for the moment
           (continue-with-program-state-tracing new-program-state trace))
          ((can-start-loop-encountered label debug-info)
           (evaluate (step-can-start-loop-encountered-tracing label debug-info new-program-state trace tracer-context)))
          ((can-close-loop-encountered label)
           (evaluate (step-can-close-loop-encountered-tracing label new-program-state tracer-context))))))
    (define (handle-response-abnormal response)
      (match response
        ((cesk-abnormal-return (cesk-stopped))
         (program-state-v (evaluator-state-struct-program-state evaluator-state)))
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
        ((? is-executing?) (evaluate (do-trace-executing-step)))
        ((? is-interpreting?) (handle-response-regular (do-cesk-interpreter-step)))
        ((? is-tracing?) (handle-response-tracing (do-cesk-interpreter-step)))
        (_ (error "Unknown state" (evaluator-state-struct-state evaluator-state)))))
    (step))
  
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
    (evaluator-state-struct INTERPRETING_STATE
                            (new-tracer-context)
                            (inject-program-state e)
                            #f))
  
  (define (run evaluator-state)
    (evaluate evaluator-state))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read))))
  
  )