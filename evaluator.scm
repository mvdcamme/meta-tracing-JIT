(module evaluator racket
  
  (require "cesk-interpreter.scm"
           "continuations.scm"
           "environment.scm"
           "interaction.scm"
           "predefined-functions.scm")
  
  (provide run)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                          Running evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (evaluate program-state)
    (define (handle-response response)
      (match response
        ((cesk-normal-return new-program-state trace annotation-signal)
         (evaluate new-program-state))
        ((cesk-abnormal-return (cesk-stopped))
         (program-state-v program-state))
        ((cesk-abnormal-return signal)
         (error "Abnormal return value from cesk interpreter" signal))))
    (handle-response (step program-state)))
  
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
  
  (define (inject e)
    (program-state (inject-ck e)
                   (add-functions-to-environment (make-new-env))
                   (add-functions-to-store (make-new-store))
                   '()
                   #f
                   `(,(haltk))))
  
  (define (run program-state)
    (evaluate program-state))
  
  ;;; Reads an s-expression from the console and runs the evaluator on it.
  (define (start)
    (run (inject (read))))
  
  )