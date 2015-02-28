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
           add-continuation
           alloc-var
           apply-native
           call-global-continuation
           create-closure
           debug
           execute-trace
           execute-guard-trace
           execute-label-trace-with-id
           execute-label-trace-with-label
           execute-mp-tail-trace
           guard-false
           guard-true
           guard-same-closure
           guard-same-nr-of-args
           literal-value
           lookup-var
           quote-value
           pop-splits-cf-id!
           pop-trace-node-frame!
           pop-trace-node-frame-until-label!
           pop-trace-node-executing!
           pop-trace-node-frame-from-stack!
           push-splits-cf-id!
           push-trace-node-frame!
           push-trace-node-executing!
           remove-continuation
           restore-env
           restore-val
           restore-vals
           save-env
           save-all-vals
           save-val
           save-vals
           set-env
           set-var
           switch-to-clo-env
           top-splits-cf-id
           top-trace-node-executing
           trace-node-frame-on-stack?
           
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
  
  ;;; Stores the general-purpose register during program execution.
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
  
  (define (get-actual-trace letrec-expression)
    (cddr (cadr (car (cadr letrec-expression)))))
  
  (define (get-letrec-body letrec-expression)
    (cddr letrec-expression))
  
  (define get-operator car)
  
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
  
  (define (execute-guard-trace guard-id)
    (let* ((guard-trace (get-guard-trace guard-id))
           (trace (trace-node-trace guard-trace))
           (corresponding-label (trace-key-label (get-trace-node-executing-trace-key))))
      ;; Benchmarking: record the fact that this trace node will be executed
      (add-execution! guard-trace)
      (execute `(let ()
                  (let* ((value (execute-trace ',trace))) ; Actually execute the trace
                    (call-global-continuation value))))))
  
  (define (execute-label-trace-with-trace-node label-trace-node)
    (let ((trace (trace-node-trace label-trace-node)))
      ;; Benchmarking: record the fact that this trace node will be executed
      (add-execution! label-trace-node)
      (execute `(let ()
                  (push-trace-node-frame! ,label-trace-node)
                  (let ((label-value (execute-trace ',trace)))
                    (pop-trace-node-frame!)
                    label-value)))))
  
  (define (execute-label-trace-with-id label-trace-id)
    (let ((label-trace-node (find (tracer-context-trace-nodes-dictionary GLOBAL_TRACER_CONTEXT) label-trace-id)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  (define (execute-label-trace-with-label label)
    (let ((label-trace-node (get-label-trace label)))
      (execute-label-trace-with-trace-node label-trace-node)))
  
  (define (execute-mp-tail-trace mp-id new-state)
    (let* ((mp-tails-dictionary (tracer-context-mp-tails-dictionary GLOBAL_TRACER_CONTEXT))
           (mp-tail-trace (get-mp-tail-trace mp-id)))
      (if mp-tail-trace
          (begin (add-execution! mp-tail-trace)
                 (let ((mp-value (execute-trace (trace-node-trace mp-tail-trace))))
                   (call-global-continuation mp-value)))
          (call-global-continuation new-state))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                    Evaluator/trace instructions                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (guard-false guard-id e)
    (if v
        (begin (output "Guard-false failed") (output-newline) (bootstrap-to-ev guard-id e))
        (begin (output "Guard passed") (output-newline))))
  
  (define (guard-true guard-id e)
    (if v
        (begin (output "Guard passed") (output-newline))
        (begin (output "Guard-true failed") (output-newline) (bootstrap-to-ev guard-id e))))
  
  (define (guard-same-closure clo i guard-id)
    (when (not (clo-equal? v clo))
      (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output v) (output-newline)
      (bootstrap-to-ko guard-id (closure-guard-failedk i))))
  
  (define (guard-same-nr-of-args i rator guard-id)
    (let ((current-i (length v)))
      (when (not (= i current-i))
        (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
        (bootstrap-to-ko (cons guard-id current-i) (apply-failedk rator current-i)))))
  
  (define (save-val)
    (when (env? v)
      (error "Save-val: saved an environment instead of a val!"))
    (set! θ (cons v θ)))
  
  (define (save-vals i)
    (when (contains-env? v)
      (error "Save-vals: saved an environment instead of a val!"))
    (set! θ (append (take v i) θ))
    (set! v (drop v i)))
  
  (define (save-all-vals)
    (when (contains-env? v)
      (error "Save-all-vals: saved an environment instead of a val!"))
    (set! θ (append v θ)))
  
  (define (save-env)
    (set! θ (cons ρ θ)))
  
  (define (set-env ρ*)
    (set! ρ ρ*))
  
  (define (restore-env)
    (set! ρ (car θ))
    (set! θ (cdr θ)))
  
  (define (restore-val)
    (set! v (car θ))
    (when (env? v)
      (error "Restore-val: restored an environment instead of a val!"))
    (set! θ (cdr θ)))
  
  (define (restore-vals i)
    (set! v (take θ i))
    (when (contains-env? v)
      (error "Restore-vals: restored an environment instead of a val!"))
    (set! θ (drop θ i)))
  
  (define (alloc-var x)
    (let ((a (new-gencounter!)))
      (set! ρ (add-var-to-env ρ x a))
      (insert! σ a v)))
  
  (define (set-var x)
    (let ((a (cdr (assoc x (env-lst ρ)))))
      (insert! σ a v)))
  
  (define (debug)
    (= 1 1))
  
  (define (lookup-var x)
    (when (eq? x 'debug) (debug))
    (let ((binding (assoc x (env-lst ρ))))
      (match binding
        ((cons _ a) (set! v (find σ a)))
        (_ (set! v (eval x))))))
  
  (define (create-closure x es)
    (set! v (clo (lam x es) ρ)))
  
  (define (literal-value e)
    (set! v e))
  
  (define (quote-value e)
    (set! v e))
  
  (define (apply-native i)
    (let ((rands (take θ i)))
      (when (contains-env? rands)
        (error "Apply-native: rands contains an environment"))
      (set! θ (drop θ i))
      (set! v (apply v rands))))
  
  (define (add-continuation φ)
    (set! τ-κ (cons φ τ-κ)))
  
  (define (remove-continuation)
    (set! τ-κ (cdr τ-κ)))
  
  (define (switch-to-clo-env i)
    (let ((clo v))
      (restore-vals i)
      (save-env)
      (save-vals i)
      (set-env (clo-ρ clo))))
  
  (define (run-trace ms)
    (for/last ((instruction ms))
      (eval instruction)))
  
  (define (execute . ms)
    (when (is-tracing?)
      (append-trace! ms))
    (run-trace ms))
  
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                     Handling tracing annotation                                      ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Is-evaluating
  ;
  
  (define (handle-is-evaluating-annotation continuation)
    (execute `(remove-continuation))
    (set-root-expression-if-uninitialised! v)
    (when (is-tracing?)
      (add-ast-node-traced! v))
    (step* continuation))
  
  ;
  ; Starting/ending trace recording
  ;
  
  (define (handle-can-close-loop-annotation label continuation)
    (output "closing annotation: tracing loop ") (output label) (output-newline)
    (when (is-tracing-label? label)
      (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
      (stop-tracing! #f))
    (execute `(remove-continuation))
    (step* continuation))
  
  (define (check-stop-tracing-label label continuation)
    (define (do-stop-tracing!)
      (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
      (stop-tracing! #t)
      (let ((new-state (execute-label-trace-with-label label)))
        (step* new-state)))
    (define (do-continue-tracing)
      (output "----------- CONTINUING TRACING -----------") (output-newline)
      (execute `(remove-continuation))
      (step* continuation))
    (inc-times-label-encountered-while-tracing!)
    (if (times-label-encountered-greater-than-threshold?)
        (do-stop-tracing!)
        (do-continue-tracing)))
  
  (define (handle-can-start-loop-annotation label debug-info continuation)
    (define (continue-with-continuation)
      (execute `(remove-continuation))
      (step* continuation))
    (cond ((is-tracing-label? label)
           (check-stop-tracing-label label continuation))
          ((label-trace-exists? label)
           (output "----------- EXECUTING TRACE -----------") (output-newline)
           (let ((label-trace (get-label-trace label)))
             (if (and (is-tracing?) (label-trace-loops? label-trace))
                 (let ((new-state (execute-label-trace-with-label label)))
                   (step* new-state))
                 (continue-with-continuation))))
          ((and (not (is-tracing?)) (>= (get-times-label-encountered label) TRACING_THRESHOLD))
           (output "----------- STARTED TRACING -----------") (output-newline)
           (start-tracing-label! label debug-info)
           (continue-with-continuation))
          (else
           (inc-times-label-encountered! label)
           (when (is-tracing?)
             (output "----------- ALREADY TRACING ANOTHER LABEL -----------") (output-newline))
           (continue-with-continuation))))
  
  ;
  ; Trace merging
  ;
  
  (define (handle-merges-cf-annotation continuation)
    (output "MERGES CONTROL FLOW") (output-newline)
    (let ((mp-id (top-splits-cf-id)))
      (execute `(remove-continuation)
               `(pop-splits-cf-id!))
      (if (is-tracing?)
          (begin
            ;(when (is-tracing-guard?)
            ;  (append-trace! `((pop-trace-node-frame!))))
            (append-trace! `(;(pop-trace-node-frame!)
                             (execute-mp-tail-trace ,mp-id ,continuation)))
            ((tracer-context-merges-cf-function GLOBAL_TRACER_CONTEXT) (reverse τ))
            (if (mp-tail-trace-exists? mp-id)
                (begin (output "MP TAIL TRACE EXISTS") (output-newline)
                       (stop-tracing-normal!)
                       (let ((new-state (eval `(execute-mp-tail-trace ,mp-id ,continuation))))
                         (step* new-state)))
                (begin (output "MP TAIL TRACE DOES NOT EXIST") (output-newline)
                       (clear-trace!)
                       (set-tracer-context-closing-function! GLOBAL_TRACER_CONTEXT (make-stop-tracing-mp-tail-function mp-id))
                       (set-tracer-context-merges-cf-function! GLOBAL_TRACER_CONTEXT (make-mp-tail-merges-cf-function mp-id))
                       (step* continuation))))
          (step* continuation))))
  
  (define (handle-splits-cf-annotation continuation)
    (execute `(remove-continuation)
             `(push-splits-cf-id! ,(inc-splits-cf-id!)))
    (step* continuation))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Running evaluator                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (eval-seq es κ)
    (match es
      ('()
       (execute `(literal-value '())
                `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((list e)
       (ev e κ))
      ((cons e es)
       (execute `(save-env)
                `(add-continuation ,(seqk es)))
       (ev e (cons (seqk es) κ)))))
  
  (define (do-function-call i κ)
    (match v
      ((clo (lam x es) ρ)
       (execute `(switch-to-clo-env ,i))
       (let loop ((i i) (x x))
         (match x
           ('()
            (unless (= i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i))
            (execute `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ)))
           ((cons x xs)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
            (execute `(restore-val)
                     `(alloc-var ',x))
            (loop (- i 1) xs))
           ((? symbol? x)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) "case 3"))
            (execute `(restore-vals ,i)
                     `(alloc-var ',x)
                     `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ))))))
      (_
       (execute `(apply-native ,i)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))))
  
  (define (step state)
    (match state
      ((ev `(and ,e . ,es) κ)
       (execute `(add-continuation ,(andk es)))
       (ev e (cons (andk es) κ)))
      ((ev `(apply ,rator ,args) κ)
       (execute `(add-continuation ,(applyk rator)))
       (ev args (cons (applyk rator) κ)))
      ((ev (? symbol? x) (cons φ κ))
       (execute `(lookup-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(begin ,es ...) κ)
       (eval-seq es κ))
      ((ev `(can-close-loop ,e) κ)
       (execute `(add-continuation ,(can-close-loopk)))
       (ev e (cons (can-close-loopk) κ)))
      ((ev `(can-start-loop ,e ,debug-info) κ)
       (execute `(add-continuation ,(can-start-loopk e '())))
       (ev debug-info (cons (can-start-loopk e '()) κ)))
      ((ev `(cond) (cons φ κ))
       (execute `(literal-value ())
                `(remove-continuation))
       (ko φ κ))      
      ((ev `(cond (else . ,es)) κ)
       (eval-seq es κ))
      ((ev `(cond (,pred . ,pes) . ,es) κ)
       (execute `(save-env)
                `(add-continuation ,(condk pes es)))
       (ev pred (cons (condk pes es) κ)))
      ((ev `(define ,pattern . ,expressions) κ)
       (if (symbol? pattern)
           (begin (execute `(save-env)
                           `(add-continuation ,(definevk pattern)))
                  (ev (car expressions) (cons (definevk pattern) κ)))
           (begin (execute `(alloc-var ',(car pattern))
                           `(create-closure ',(cdr pattern) ',expressions)
                           `(set-var ',(car pattern))
                           `(remove-continuation))
                  (match κ
                    ((cons φ κ) (ko φ κ))))))
      ((ev `(if ,e ,e1 . ,e2) κ)
       (execute `(save-env)
                `(add-continuation ,(ifk e1 e2)))
       (ev e (cons (ifk e1 e2) κ)))
      ((ev `(is-evaluating ,e) κ)
       (execute `(add-continuation ,(is-evaluatingk)))
       (ev e (cons (is-evaluatingk) κ)))
      ((ev `(lambda ,x ,es ...) (cons φ κ))
       (execute `(create-closure ',x ',es)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(let () . ,expressions)  κ)
       (eval-seq expressions κ))
      ((ev `(let ((,var ,val) . ,bds) . ,es) κ)
       (unless (null? bds)
         (error "Syntax error: let used with more than one binding: " bds))
       (execute `(save-env)
                `(add-continuation ,(letk var es)))
       (ev val (cons (letk var es) κ)))
      ((ev `(let* () . ,expressions) κ)
       (eval-seq expressions κ))
      ((ev `(let* ((,var ,val) . ,bds) . ,es) κ)
       (execute `(save-env)
                `(add-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ev `(letrec ((,x ,e) . ,bds) . ,es) κ)
       (execute `(literal-value '())
                `(alloc-var ',x)
                `(save-env)
                `(add-continuation ,(letreck x bds es)))
       (ev e (cons (letreck x bds es) κ)))
      ((ev `(or ,e . ,es) κ)
       (execute `(add-continuation ,(ork es)))
       (ev e (cons (ork es) κ)))
      ((ev `(quote ,e) (cons φ κ))
       (execute `(quote-value ',e)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(set! ,x ,e) κ)
       (execute `(save-env)
                `(add-continuation ,(setk x)))
       (ev e (cons (setk x) κ)))
      ((ev `(,rator) κ)
       (execute `(save-env)
                `(add-continuation ,(ratork 0 'regular-nulary)))
       (ev rator (cons (ratork 0 'regular-nulary) κ)))
      ((ev `(,rator . ,rands) κ)
       (execute `(save-env))
       (let ((rrands (reverse rands)))
         (execute `(add-continuation ,(randk rator (cdr rrands) 1)))
         (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
      ((ev e (cons φ κ))
       (execute `(literal-value ,e)
                `(remove-continuation))
       (ko φ κ))
      ((ko (andk '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (andk '()) (cons φ κ))
       (execute `(remove-continuation))
       (ko φ κ))
      ((ko (andk es) κ)
       (if v
           (begin (execute `(add-continuation ,(andk (cdr es))))
                  (ev (car es) (cons (andk (cdr es)) κ)))
           (begin (execute `(remove-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (applicationk debug) κ)
       (execute `(restore-env)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (apply-failedk rator i) κ)
       (execute `(save-all-vals)
                `(save-env)
                `(add-continuation ,(ratork i 'apply)))
       (ev rator (cons (ratork i 'apply) κ)))
      ((ko (applyk rator) κ)
       (let ((i (length v)))
         (execute `(guard-same-nr-of-args ,i ',rator ,(inc-guard-id!))
                  `(save-all-vals)
                  `(save-env)
                  `(add-continuation ,(ratork i 'apply)))
         (ev rator (cons (ratork i 'apply) κ))))
      ((ko (closure-guard-failedk i) κ)
       (do-function-call i κ))
      ((ko (condk pes '()) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) '()))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                           `(literal-value '())
                           `(remove-continuation))
                  (ko (car κ) (cdr κ)))))
      ((ko (condk pes `((else . ,else-es))) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',`(begin ,@else-es)))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes)))
                  (eval-seq else-es κ))))
      ((ko (condk pes `((,pred . ,pred-es) . ,es)) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',`(cond ,@es)))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',`(begin ,@pes))
                           `(save-env)
                           `(add-continuation ,(condk pred-es es)))
                  (ev pred (cons (condk pred-es es) κ)))))
      ((ko (definevk x) (cons φ κ))
       (execute `(restore-env)
                `(alloc-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ko (haltk) _)
       #f) 
      ((ko (ifk e1 e2) κ)
       (execute `(restore-env))
       (let ((new-guard-id (inc-guard-id!)))
         (if v
             (begin (execute `(guard-true ,new-guard-id ',(if (null? e2)
                                                              '()
                                                              ;; If the guard fails, the predicate was false, so e2 should be evaluated
                                                              (car e2)))) 
                    (ev e1 κ))
                    ;; If the guard fails, the predicate was true, so e1 should be evaluated
             (begin (execute `(guard-false ,new-guard-id ',e1)) 
                    (if (null? e2)
                        (begin (execute `(remove-continuation)
                                        `(literal-value '()))
                               (ko (car κ) (cdr κ)))
                        (ev (car e2) κ))))))
      ((ko (letk x es) κ)
       (execute `(restore-env)
                `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x '() es) κ)
       (execute `(restore-env)
                `(alloc-var ',x))
       (eval-seq es κ))
      ((ko (let*k x `((,var ,val) . ,bds) es) κ)
       (execute `(restore-env)
                `(alloc-var ',x)
                `(save-env)
                `(add-continuation ,(let*k var bds es)))
       (ev val (cons (let*k var bds es) κ)))
      ((ko (letreck x '() es) κ)
       (execute `(restore-env)
                `(set-var ',x))
       (eval-seq es κ))
      ((ko (letreck x `((,var ,val) . ,bds) es) κ)
       (execute `(restore-env)
                `(set-var ',x)
                `(alloc-var ',var)
                `(save-env)
                `(add-continuation ,(letreck var bds es)))
       (ev val (cons (letreck var bds es) κ)))
      ((ko (ork '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (ork es) κ)
       (if v
           (begin (execute `(remove-continuation))
                  (ko (car κ) (cdr κ)))
           (ev `(or ,@es) κ)))
      ((ko (randk rator '() i) κ)
       (execute `(restore-env)
                `(save-val)
                `(save-env)
                `(add-continuation ,(ratork i 'regular)))
       (ev rator (cons (ratork i 'regular) κ)))
      ((ko (randk rator rands i) κ)
       (execute `(restore-env)
                `(save-val)
                `(save-env)
                `(add-continuation ,(randk rator (cdr rands) (+ i 1))))
       (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
      ((ko (ratork i debug) κ)
       (execute `(restore-env)
                `(guard-same-closure ,v ,i  ,(inc-guard-id!)))
       (do-function-call i κ))
      ((ko (seqk '()) (cons φ κ)) ; No tailcall optimization!
       (execute `(restore-env)
                `(remove-continuation))
       (ko φ κ))
      ((ko (seqk (cons e exps)) κ)
       (execute `(add-continuation ,(seqk exps)))
       (ev e (cons (seqk exps) κ)))
      ((ko (setk x) (cons φ κ))
       (execute `(restore-env)
                `(set-var ',x)
                `(remove-continuation))
       (ko φ κ))))
  
  (define (step* s)
    (match s
      ((ko (haltk) _)
       v)
      ((ko (is-evaluatingk) (cons φ κ))
       (handle-is-evaluating-annotation (ko φ κ)))
      ((ev `(splits-control-flow) (cons φ κ))
       (handle-splits-cf-annotation (ko φ κ)))
      ((ev `(merges-control-flow) (cons φ κ))
       (handle-merges-cf-annotation (ko φ κ)))
      ((ko (can-close-loopk) (cons φ κ))
       (handle-can-close-loop-annotation v (ko φ κ)))
      ((ko (can-start-loopk label '()) κ)
       (execute `(add-continuation ,(can-start-loopk '() v)))
       (step* (ev label (cons (can-start-loopk '() v) κ))))
      ((ko (can-start-loopk '() debug-info) (cons φ κ))
       (handle-can-start-loop-annotation v debug-info (ko φ κ)))
      (_
       (let ((new-state (step s)))
         (step* new-state)))))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                           Bootstrapping                                              ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (switch-to-trace-guard! guard-id old-trace-key)
    (stop-tracing-abnormal!)
    (start-tracing-guard! guard-id old-trace-key))
  
  (define (bootstrap guard-id state)
    (output "------ BOOTSTRAP: GUARD-ID: ") (output guard-id) (output " ------") (output-newline)
    (cond ((guard-trace-exists? guard-id)
           (output "----------- STARTING FROM GUARD ") (output guard-id) (output " -----------") (output-newline)
           (execute-guard-trace guard-id))
          ((not (is-tracing?))
           (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
           (let* ((trace-key-executing (get-trace-node-executing-trace-key))
                  (corresponding-label (trace-key-label trace-key-executing)))
             ;; Trace-nodes executing stack will be flushed
             (call-global-continuation state)
             (start-tracing-guard! guard-id trace-key-executing)))
          (else
           ;; Interpreter is tracing, has traced a jump to an existing (inner) trace and in this
           ;; inner trace a guard-failure has now occurred. Abandon the existing trace and start
           ;; tracing from this new guard-failure.
           (output "----------- ABANDONING CURRENT TRACE; SWITCHING TO TRACE GUARD: ") (output guard-id) (output-newline)
           (let ((trace-key-executing (get-trace-node-executing-trace-key)))
             (switch-to-trace-guard! guard-id trace-key-executing)
             (call-global-continuation state)))))
  
  (define (bootstrap-to-ev guard-id e)
    (bootstrap guard-id (ev e τ-κ)))
  
  (define (bootstrap-to-ko guard-id φ)
    (bootstrap guard-id (ko φ τ-κ)))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Starting evaluator                                           ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Resetting evaluator
  ;
  
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
  
  (define (inject e)
    (ev e `(,(haltk))))
  
  (define (run s)
    (reset!)
    (apply step* (list (let ((v (call/cc (lambda (k)
                                           (set-global-continuation! k)
                                           s))))
                         (flush-trace-nodes-executing!)
                         v))))
  
  (define (start)
    (run (inject (read)))))