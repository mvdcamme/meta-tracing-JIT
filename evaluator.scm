(module evaluator racket
  
  (require (rename-in "cesk-interpreter.scm"
                      (step cesk-step))
           "continuations.scm"
           "environment.scm"
           "interaction.scm"
           "predefined-functions.scm"
           "tracing.scm")
  
  (provide run)
  
  
  ;
  ; Constants
  ;
  
  (define MAX_TIMES_LABEL_ENCOUNTERED 5)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                          Running evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (struct evaluator-state (tracer-context
                           program-state
                           trace-executing) #:transparent)
  
  (define (evaluate evaluator-state)
    (define (do-cesk-interpreter-step)
      (cesk-step (evaluator-state-program-state evaluator-state)))
    (define (do-trace-executing-step)
      ; TODO
      #f)
    (define (handle-annotation-signal new-program-state trace annotation-signal)
      ; TODO
      #f)
    (define (handle-response-regular response)
      (match response
        ((cesk-normal-return new-program-state trace #f)
         (evaluate new-program-state))
        ((cesk-normal-return new-program-state trace annotation-signal)
         (handle-annotation-signal new-program-state trace annotation-signal))
        ((cesk-abnormal-return (cesk-stopped))
         (program-state-v program-state))
        ((cesk-abnormal-return signal)
         (error "Abnormal return value from cesk interpreter" signal))))
    (define (step tracer-context)
      (cond ((is-regular-interpreting? tracer-context) (handle-response-regular (do-cesk-interpreter-step)))
            ((is-tracing? tracer-context) (handle-response-tracing (do-cesk-interpreter-step)))
            ((is-executing-trace? tracer-context) (handle-response-executing (do-trace-executing-step)))
            (else (error "Unknown state" (tracer-context-state tracer-context)))))
    (handle-response (do-cesk-interpreter-step)))
  
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
  
  (define (inject-evaluator-state e)
    (evaluator-state (new-tracer-context)
                     (inject-program-state e)))
  
  (define (run evaluator-state)
    (evaluate evaluator-state))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject-evaluator-state (read))))
  
  )