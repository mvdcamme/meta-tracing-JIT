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
  ;                                          Running evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (struct evaluator-state (tracer-context
                           program-state
                           trace-executing) #:transparent)
  
  (define-syntax evaluator-state-copy
    (syntax-rules ()
      ((_ an-evaluator-state ...)
       (struct-copy evaluator-state an-evaluator-state ...))))
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-regular label new-program-state tracer-context)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (evaluator-state tracer-context
                     new-program-state
                     #f))
  
  ;;; Handles the (can-close-loop label) annotation and afterwards continues
  ;;; regular interpretation with the given state.
  (define (step-can-close-loop-encountered-tracing label new-program-state tracer-context)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (if (is-tracing-label? tracer-context label)
        (evaluator-state (stop-tracing tracer-context #f)
                         new-program-state
                         #f)
        (evaluator-state tracer-context
                         new-program-state
                         #f)))
  
  (define (step-can-start-loop-encountered-regular label debug-info new-program-state tracer-context)
    (define (can-start-tracing-label?)
      (>= (get-times-label-encountered tracer-context label) TRACING_THRESHOLD))
    (cond ((label-trace-exists? tracer-context label)
           (output "----------- EXECUTING TRACE -----------") (output-newline)
           (evaluator-state (set-executing-trace-state tracer-context)
                            program-state
                            (get-label-trace tracer-context label)))
          ;; We have determined that it is worthwile to trace this label/loop, so start tracing.
          ((can-start-tracing-label?)
           (output "----------- STARTED TRACING -----------") (output-newline)
           (evaluator-state (start-tracing-label tracer-context label debug-info)
                            new-program-state
                            #f))
          ;; Increase the counter for the number of times this label has been encountered
          ;; (i.e., we raise the 'hotness' of this loop).
          (else
           (evaluator-state (inc-times-label-encountered tracer-context label)
                            new-program-state
                            #f))))
  
  (define (step-can-start-loop-encountered-tracing label debug-info new-program-state tracer-context)
    (cond ((is-tracing-label? tracer-context label)
           (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
           (let* ((temp-tracer-context (stop-tracing tracer-context #t))
                  (trace-node (get-label-trace temp-tracer-context label))
                  (trace (trace-node-trace trace-node)))
             (evaluator-state (set-executing-trace-state temp-tracer-context)
                              new-program-state
                              trace)))
          ;; Increase the counter for the number of times this label has been encountered
          ;; (i.e., we raise the 'hotness' of this loop).
          (else
           (evaluator-state (inc-times-label-encountered tracer-context label)
                            new-program-state
                            #f))))
  
  (define (evaluate evaluator-state)
    (define (continue-with-program-state-regular new-program-state)
      (evaluate (evaluator-state-copy evaluator-state
                                      (program-state new-program-state))))
    (define (continue-with-program-state-tracing new-program-state new-trace)
      (evaluate (evaluator-state-copy evaluator-state
                                      (tracer-context (append-trace tracer-context trace))
                                      (program-state new-program-state))))
    (define (do-cesk-interpreter-step)
      (cesk-step (evaluator-state-program-state evaluator-state)))
    (define (do-trace-executing-step)
      ; TODO
      #f)
    (define (handle-response-executing new-program-state signal)
      ; TODO
      #f)
    (define (handle-annotation-signal-regular new-program-state trace annotation-signal)
      (match annotation-signal
        ((is-evaluating-encountered _)
         ;; TODO Just ignore for the moment
         (continue-with-program-state-regular new-program-state))
        ((can-start-loop-encountered label debug-info)
         (evaluate (step-can-start-loop-encountered-regular label debug-info new-program-state (evaluator-state-tracer-context evaluator-state))))
        ((can-close-loop-encountered label)
         (evaluate (step-can-close-loop-encountered-regular label new-program-state (evaluator-state-tracer-context evaluator-state))))))
    (define (handle-annotation-signal-tracing new-program-state trace annotation-signal)
      (match annotation-signal
        ((is-evaluating-encountered _)
         ;; TODO Just ignore for the moment
         (continue-with-program-state-tracing new-program-state trace))
        ((can-start-loop-encountered label debug-info)
         (evaluate (step-can-start-loop-encountered-tracing label debug-info new-program-state (evaluator-state-tracer-context evaluator-state))))
        ((can-close-loop-encountered label)
         (evaluate (step-can-close-loop-encountered-tracing label new-program-state (evaluator-state-tracer-context evaluator-state))))))
    (define (handle-response-abnormal response)
      (match response
        ((cesk-abnormal-return (cesk-stopped))
         (program-state-v (evaluator-state-program-state evaluator-state)))
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
    (define (handle-response-tracing new-program-state trace annotation-signal)
      (match response
        ((cesk-normal-return new-program-state _ #f)
         (continue-with-program-state-tracing new-program-state))
        ((cesk-normal-return new-program-state trace annotation-signal)
         (handle-annotation-signal-tracing new-program-state trace annotation-signal))
        (_
         (handle-response-abnormal response))))
    (define (step tracer-context)
      (cond ((is-regular-interpreting? tracer-context) (handle-response-regular (do-cesk-interpreter-step)))
            ((is-tracing? tracer-context) (handle-response-tracing (do-cesk-interpreter-step)))
            ((is-executing-trace? tracer-context) (handle-response-executing (do-trace-executing-step)))
            (else (error "Unknown state" (tracer-context-state tracer-context)))))
    (step (evaluator-state-tracer-context evaluator-state)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Starting evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    
  ;;; Creates a new store that contains all predefined functions/variables.
  (define (make-new-store)
    '())
  
  ;;; Transforms the given expression into a CK state, so that it can be used by the evaluator.
  (define (inject-ck e)
    (ev e `(,(haltk))))
  
  (define (inject-program-state e)
    (program-state (inject-ck e)
                   (add-functions-to-environment (make-new-env))
                   (add-functions-to-store (make-new-store))
                   '()
                   #f
                   `(,(haltk))))
  
  (define (inject e)
    (evaluator-state (new-tracer-context)
                     (inject-program-state e)
                     #f))
  
  (define (run evaluator-state)
    (evaluate evaluator-state))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read))))
  
  )