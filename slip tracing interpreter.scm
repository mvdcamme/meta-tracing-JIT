(module tracing-interpreter racket
  (provide inject
           run
           
           ;;structs
           ev
           ko
           sentinel
           
           sentinel?
           unwrap-possible-sentinel
           
           ;;registers
           τ-κ
           
           ;;trace instructions
           add-continuation
           alloc-var
           apply-native
           call-label-trace!
           create-closure
           debug
           guard-false
           guard-true
           guard-same-closure
           guard-same-nr-of-args
           literal-value
           lookup-var
           quote-value
           pop-continuation!
           pop-guard-id!
           pop-head-executing!
           pop-trace-node-frame-from-stack!
           pop-trace-frame!
           pop-trace-frame-until-label!
           push-guard-id!
           push-continuation!
           push-head-executing!
           push-trace-frame!
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
           start-executing-label-trace!
           switch-to-clo-env
           top-continuation
           
           ;;metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length)
  
  
  (require "dictionary.scm")
  (require "stack.scm")
  
  ;
  ; constants
  ;
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define ENABLE_OUTPUT #f)
  (define TRACING_THRESHOLD 5)
  
  (define ns (make-base-namespace))
  
  ;
  ; misc
  ;
  
  (define guard-id 0)
  
  (define (inc-guard-id!)
    (let ((temp guard-id))
      (set! guard-id (+ guard-id 1))
      temp))
  
  (define (output s)
    (if ENABLE_OUTPUT
        (display s)
        (void)))
  
  (define (output-newline)
    (output #\newline))
  
  (define (massoc el lst)
    (cond ((null? lst) #f)
          ((eq? el (mcar (car lst))) (car lst))
          (else (massoc el (cdr lst)))))
  
  (define (clo-equal? clo1 clo2)
    (or (eq? clo1 clo2)
        (and (clo? clo1)
             (clo? clo2)
             (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
             (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2))))))
  
  (struct sentinel (value) #:transparent)
  
  (define (unwrap-possible-sentinel value)
    (if (sentinel? value)
        (car (sentinel-value value))
        value))
  
  ;
  ; continuations
  ;
  
  (struct ev (e κ) #:transparent)
  (struct ko (φ κ) #:transparent)
  (struct andk (es))
  (struct apply-failedk (rator i))
  (struct applicationk (debug))
  (struct applyk (rator))
  (struct can-close-loopk (debug-info) #:transparent)
  (struct can-start-loopk (debug-info) #:transparent)
  (struct clo (λ ρ))
  (struct closure-guard-failedk (i))
  (struct condk (pes es))
  (struct definevk (x)) ;define variable
  (struct haltk ())
  (struct ifk (e1 e2))
  (struct lam (x es))
  (struct letk (x es))
  (struct let*k (x bds es))
  (struct letreck (x bds es))
  (struct ork (es))
  (struct randk (e es i) #:transparent)
  (struct ratork (i debug))
  (struct seqk (es) #:transparent)
  (struct setk (x))
  
  ;
  ; registers
  ;
  
  (define ρ #f) ; env
  (define σ #f) ; store
  (define θ #f) ; non-kont stack
  (define v #f) ; value
  (define τ #f) ; trace
  
  (define τ-κ #f) ;continuation stack
  
  ;
  ;tracing
  ;
  
  (struct trace-key (label
                     guard-ids) #:transparent)
  
  (define (is-tracing-guard? trace-key)
    (not (eq? (trace-key-guard-ids trace-key) '())))
  
  (struct trace-node (label
                      trace
                      (children #:mutable)))
  
  (define (make-trace-node label trace)
    (trace-node label trace '()))
  
  (struct tracer-context (is-tracing?
                          trace-key-to-be-traced
                          save-next-guard-id?
                          trace-nodes
                          labels-encountered
                          heads-executing
                          guards-id-stack
                          continuation-calls-stack
                          closing-function) #:transparent #:mutable)
  
  (define (new-tracer-context)
    (tracer-context #f
                    #f
                    #f
                    '()
                    '()
                    '()
                    (new-stack)
                    (new-stack)
                    #f))
  
  (define (is-tracing?)
    (tracer-context-is-tracing? global-tracer-context))
  
  (define (is-tracing-label? label)
    (and (tracer-context-trace-key-to-be-traced global-tracer-context)
         (equal? (trace-key-label (tracer-context-trace-key-to-be-traced global-tracer-context)) label)))
  
  (define (get-times-label-encountered label)
    (let ((pair (massoc label (tracer-context-labels-encountered global-tracer-context))))
      (if pair
          (mcdr pair)
          0)))
  
  (define (inc-times-label-encountered! label)
    (let ((pair (massoc label (tracer-context-labels-encountered global-tracer-context))))
      (if pair
          (set-mcdr! pair (+ (mcdr pair) 1))
          (set-tracer-context-labels-encountered! global-tracer-context 
                                                  (cons (mcons label 1) (tracer-context-labels-encountered global-tracer-context))))))
  
  (define (get-head-executing)
    (let ((heads-executing (tracer-context-heads-executing global-tracer-context)))
      (if (null? heads-executing)
          (error "Heads-executing stack is empty!")
          (car heads-executing))))
  
  (define (push-head-executing! trace-node)
    (let ((heads-executing (tracer-context-heads-executing global-tracer-context)))
      (set-tracer-context-heads-executing! global-tracer-context
                                           (cons trace-node heads-executing))))
  
  (define (pop-head-executing!)
    (let ((heads-executing (tracer-context-heads-executing global-tracer-context)))
      (if (null? heads-executing)
          (error "Heads-executing stack is empty!")
          (set-tracer-context-heads-executing! global-tracer-context
                                               (cdr heads-executing)))))
  
  (define (pop-continuation!)
    (pop! (tracer-context-continuation-calls-stack global-tracer-context)))
  
  (define (push-continuation! k)
    (push! (tracer-context-continuation-calls-stack global-tracer-context) k))
  
  (define (pop-trace-frame!)
    (pop-head-executing!)
    (pop-continuation!))
  
  (define (pop-trace-frame-until-label! label)
    (let ((current-head-executing (get-head-executing)))
      (define (loop current-head-executing)
        (and (not (equal? (trace-node-label current-head-executing) label))
             (begin (pop-trace-frame!)
                    (loop (get-head-executing)))))
      (loop current-head-executing)))
  
  (define (push-trace-frame! head-executing continuation)
    (push-head-executing! head-executing)
    (push-continuation! continuation))
  
  (define (top-continuation)
    (top (tracer-context-continuation-calls-stack global-tracer-context)))
  
  (define (find-trace-node label)
    (define (loop trace-nodes)
      (cond ((null? trace-nodes) #f)
            ((equal? (trace-node-label (car trace-nodes)) label) (car trace-nodes)) ;TODO verander equal? naar eq?
            (else (loop (cdr trace-nodes)))))
    (loop (tracer-context-trace-nodes global-tracer-context)))
  
  (define (get-trace-node label)
    (let ((trace-node-found (find-trace-node label)))
      (if trace-node-found
          trace-node-found
          (error "Label was not found in global-tracer-context: " label))))
  
  (define (label-traced? label)
    (not (eq? (find-trace-node label) #f)))
  
  (define (add-label-trace! label transformed-trace)
    (set-tracer-context-trace-nodes! global-tracer-context
                                     (cons (make-trace-node label transformed-trace)
                                           (tracer-context-trace-nodes global-tracer-context))))
  
  ;guard-ids should go from the top of the tree to the bottom
  (define (find-guard-trace label guard-ids)
    (let ((first-trace-node (get-trace-node label)))
      (define (find-next-node-in-path trace-node guard-id)
        (define (loop children)
          (cond ((null? children) (error "Trace-key was not found: " (trace-key label guard-ids)))
                ((equal? (trace-node-label (car children)) guard-id) (car children))
                (else (loop (cdr children)))))
        (loop (trace-node-children trace-node)))
      (define (follow-path trace-node guard-ids)
        (if (null? (cdr guard-ids))
            trace-node
            (follow-path (find-next-node-in-path trace-node (car guard-ids)) (cdr guard-ids))))
      (follow-path first-trace-node guard-ids)))
  
  (define (add-guard-trace! label guard-ids trace)
    (let ((parent-trace-node (find-guard-trace label guard-ids))
          (new-guard-id (last guard-ids)))
      (set-trace-node-children! parent-trace-node
                                (cons (make-trace-node new-guard-id trace)
                                      (trace-node-children parent-trace-node)))))
  
  (define (get-guard-trace guard-id)
    (let ((head-executing-children (trace-node-children (get-head-executing))))
      (define (loop lst)
        (cond ((null? lst) #f)
              ((equal? (trace-node-label (car lst)) guard-id) (car lst))
              (else (loop (cdr lst)))))
      (loop head-executing-children)))
  
  (define (start-tracing-label! label)
    (clear-trace!)
    (set-tracer-context-is-tracing?! global-tracer-context #t)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context (trace-key label '())))
  
  (define (generate-guard-trace-key)
    (let* ((list (reverse (tracer-context-heads-executing global-tracer-context)))
           (top-label (trace-node-label (car list)))
           (guards (cdr list))
           (guard-ids-path '()))
      (define (loop list)
        (cond ((null? list) '())
              ((pair? (trace-node-label (car list))) (display "## found a symbol! ##") (newline) '())
              (else (set! guard-ids-path (cons (trace-node-label (car list)) guard-ids-path))
                    (loop (cdr list)))))
      (loop guards)
      (trace-key top-label guard-ids-path)))
  
  (define (start-tracing-after-guard! guard-id old-trace-key)
    (clear-trace!)
    (set-tracer-context-closing-function! global-tracer-context (make-stop-tracing-after-guard-function))
    (set-tracer-context-is-tracing?! global-tracer-context #t)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context (trace-key (trace-key-label old-trace-key)
                                                                                 (cons guard-id (trace-key-guard-ids old-trace-key)))))
  
  (define (start-executing-label-trace! label)
    (let* ((trace-node (get-trace-node label))
           (trace (trace-node-trace trace-node)))
      (execute `(let ((value (call/cc (lambda (k)
                                        (push-trace-frame! ,trace-node k)
                                        (eval ,trace)
                                        (ko (car τ-κ) (cdr τ-κ))))))
                  (pop-trace-frame!)
                  (let ((kk (top-continuation)))
                    (and (not (sentinel? value))
                         (remove-continuation))
                    ;(output "in start-executing-label-trace!: sentinel? ")  (output (sentinel? value)) (output ", value = ") (output value) (output-newline)
                    (kk (sentinel (list (unwrap-possible-sentinel value)))))))))
  
  (define (push-guard-id! guard-id)
    (push! (tracer-context-guards-id-stack global-tracer-context) guard-id))
  
  (define (pop-guard-id!)
    (pop! (tracer-context-guards-id-stack global-tracer-context)))
  
  (define (save-next-guard-id?)
    (tracer-context-save-next-guard-id? global-tracer-context))
  
  (define (set-closing-function-if-not-yet-existing! closing-function)
    (or (tracer-context-closing-function global-tracer-context)
        (set-tracer-context-closing-function! global-tracer-context closing-function)))
  
  ;
  ; Transform trace
  ;
  
  
  
  (define (transform-trace trace loop-closed?)
    (if loop-closed?
        `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
           (loop))
        `(letrec ((non-loop ,(append '(lambda ()) trace)))
           (non-loop))))
  
  ;
  ; Optimize trace
  ;
  
  (define (changes-env? instruction)
    (or (eq? instruction 'guard-false)
        (eq? instruction 'guard-true)
        (eq? instruction 'guard-same-closure)
        (eq? instruction 'alloc-var)
        (eq? instruction 'set-env)
        (eq? instruction 'switch-to-clo-env)))
  
  ;#f = don't copy the instruction into the final trace
  ;#t = do copy the instruction into the final trace
  
  (define (save-last-env-save stack)
    (set-mcdr! (car stack) #t))
  
  (define (save-all-env-saves stack)
    (for-each (lambda (pair)
                (set-mcdr! pair #t))
              stack))
  
  (define (copy-relevant-instructions list)
    (define (loop to-copy copied)
      (cond ((null? to-copy) (reverse copied))
            ((mcdr (car to-copy)) (loop (cdr to-copy) (cons (mcar (car to-copy)) copied)))
            (else (loop (cdr to-copy) copied))))
    (loop list '()))
  
  (define (optimize-trace trace)
    (define (first-run trace stack first-run-through)
      (cond ((null? trace) (save-all-env-saves stack) (reverse first-run-through))
            ((eq? (caar trace) 'save-env)
             (let ((pair (mcons (car trace) #f)))
               (first-run (cdr trace) (cons pair stack) (cons pair first-run-through))))
            ((eq? (caar trace) 'restore-env)
             (cond ((null? stack)
                    (let ((pair (mcons (car trace) #t)))
                      (first-run (cdr trace) stack (cons pair first-run-through))))
                   ((mcdr (car stack))
                    ;The environment should be saved and restored
                    (let ((pair (mcons (car trace) #t)))
                      (first-run (cdr trace) (cdr stack) (cons pair first-run-through))))
                   (else 
                    (let ((pair (mcons (car trace) #f)))
                      ;Not really necessary to add the pair to the first-run-through list
                      (first-run (cdr trace) (cdr stack) (cons pair first-run-through))))))
            ((changes-env? (caar trace))
             (let ((pair (mcons (car trace) #t)))
               (and (not (null? stack)) (save-last-env-save stack))
               (first-run (cdr trace) stack (cons pair first-run-through))))
            (else
             (let ((pair (mcons (car trace) #t)))
               (first-run (cdr trace) stack (cons pair first-run-through))))))
    (define first-run-through (first-run trace '() '()))
    (copy-relevant-instructions first-run-through))
  
  (define (stop-tracer-context-tracing!)
    (set-tracer-context-is-tracing?! global-tracer-context #f)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context #f)
    (set-tracer-context-closing-function! global-tracer-context #f))
  
  (define (transform-and-optimize-trace trace transformation-function)
    (if ENABLE_OPTIMIZATIONS
        (transformation-function (optimize-trace trace))
        (transformation-function trace)))
  
  (define (transform-label-trace-looping trace)
    `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
       (loop)))
  
  (define (transform-label-trace-non-looping trace)
    `(letrec ((non-loop ,(append '(lambda ()) trace)))
       (non-loop)))
  
  (define (make-transform-label-trace-function looping?)
    (if looping?
        transform-label-trace-looping
        transform-label-trace-non-looping))
  
  (define (make-stop-tracing-after-label-function)
    (define (stop-tracing-label! trace looping?)
      (let ((transformed-trace (transform-and-optimize-trace trace (make-transform-label-trace-function looping?))))
        (add-label-trace! (trace-key-label (tracer-context-trace-key-to-be-traced global-tracer-context)) transformed-trace)))
    stop-tracing-label!)
  
  (define (pop-trace-node-frame-from-stack! label)
    ;Keep popping the trace frames from the stack until the top of the stack is the trace frame for this label.
    ;Then pop one more time to get it off the stack.
    (pop-trace-frame-until-label! label)
    (pop-trace-frame!))
  
  (define (call-label-trace! label)
    (execute `(pop-trace-node-frame-from-stack! ',label))
    (start-executing-label-trace! label))
  
  (define (make-transform-guard-trace-looping label)
    (define (transform-guard-trace-looping trace)
      `(letrec ((non-loop ,(append '(lambda ()) trace)))
         (non-loop)
         (output "----------- EXECUTING TRACE ") (output ',label) (output " -----------") (output-newline)
         (call-label-trace! ',label)))
    transform-guard-trace-looping)
  
  (define transform-guard-trace-non-looping transform-label-trace-non-looping)
  
  (define (make-transform-guard-trace-function label looping?)
    (if looping?
        (make-transform-guard-trace-looping label)
        transform-guard-trace-non-looping))
  
  (define (make-stop-tracing-after-guard-function)
    (define (stop-tracing-after-guard! trace looping?)
      (let* ((trace-key (tracer-context-trace-key-to-be-traced global-tracer-context))
             (label (trace-key-label trace-key))
             (guard-ids (trace-key-guard-ids trace-key))
             (transformed-trace (transform-and-optimize-trace trace (make-transform-guard-trace-function label looping?))))
        (add-guard-trace! label (reverse guard-ids) transformed-trace)))
    stop-tracing-after-guard!)
  
  (define (stop-tracing! looping?)
    (let ((stop-tracing-function (tracer-context-closing-function global-tracer-context)))
      (stop-tracing-function (reverse τ) looping?)
      (stop-tracer-context-tracing!)))
  
  (define global-tracer-context #f)
  
  (define (calculate-total-number-of-traces)
    (define sum 0)
    (define (tree-rec lst)
      (for-each (lambda (child)
                  (set! sum (+ sum 1))
                  (tree-rec (trace-node-children child)))
                lst))
    (for-each (lambda (global-trace-nodes)
                (set! sum (+ sum 1))
                (tree-rec (trace-node-children global-trace-nodes)))
              (tracer-context-trace-nodes global-tracer-context))
    sum)
  
  (define (calculate-total-traces-length)
    (define sum 0)
    (define (tree-rec lst)
      (for-each (lambda (child)
                  (set! sum (+ sum (length (cddadr (caadr (trace-node-trace child))))))
                  (tree-rec (trace-node-children child)))
                lst))
    (for-each (lambda (global-trace-nodes)
                (set! sum (+ sum (length (cddadr (caadr (trace-node-trace global-trace-nodes))))))
                (tree-rec (trace-node-children global-trace-nodes)))
              (tracer-context-trace-nodes global-tracer-context))
    sum)
  
  (define (calculate-average-trace-length)
    (let ((total-number-of-traces (calculate-total-number-of-traces)))
      (if (= total-number-of-traces 0)
          "No traces were formed"
          (/ (calculate-total-traces-length) total-number-of-traces))))
  
  ;
  ;evaluation
  ;
  
  (define (guard-false guard-id e)
    (if v
        (begin (output "Guard-false failed") (output-newline) (bootstrap-to-ev guard-id e))
        (begin (output "Guard passed") (output-newline))))
  
  (define (guard-true guard-id e)
    (if v
        (begin (output "Guard passed") (output-newline))
        (begin (output "Guard-true failed") (output-newline) (bootstrap-to-ev guard-id e))))
  
  (define (guard-same-closure clo i guard-id)
    (and (not (clo-equal? v clo))
         (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output v) (output-newline)
         (bootstrap-to-ko guard-id (closure-guard-failedk i))))
  
  (define (guard-same-nr-of-args i rator guard-id)
    (let ((current-i (length v)))
      (and (not (= i current-i))
           (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
           (bootstrap-to-ko (cons guard-id current-i) (apply-failedk rator current-i)))))
  
  (define (contains-env? lst)
    (cond ((null? lst) #f)
          ((env? (car lst)) #t)
          (else (contains-env? (cdr lst)))))
  
  (define (save-val)
    (and (env? v)
         (error "Save-val: saved an environment instead of a val!"))
    (set! θ (cons v θ)))
  
  (define (save-vals i)
    (and (contains-env? v)
         (error "Save-vals: saved an environment instead of a val!"))
    (set! θ (append (take v i) θ))
    (set! v (drop v i)))
  
  (define (save-all-vals)
    (and (contains-env? v)
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
    (and (env? v)
         (error "Restore-val: restored an environment instead of a val!"))
    (set! θ (cdr θ)))
  
  (define (restore-vals i)
    (set! v (take θ i))
    (and (contains-env? v)
         (error "Restore-vals: restored an environment instead of a val!"))
    (set! θ (drop θ i)))
  
  (define (alloc-var x)
    (let ((a (gensym)))
      (set! ρ (add-var-to-env ρ x a))
      (set! σ (cons (cons a v) σ))))
  
  (define (set-var x)
    (let ((a (cdr (assoc x (env-lst ρ)))))
      (set! σ (cons (cons a v) σ))))
  
  (define (debug)
    (= 1 1))
  
  (define (lookup-var x)
    (and (eq? x 'debug) (debug))
    (let ((binding (assoc x (env-lst ρ))))
      (match binding
        ((cons _ a) (set! v (cdr (assoc a σ))))
        (_ (set! v (eval x))))))
  
  (define (create-closure x es)
    (set! v (clo (lam x es) ρ)))
  
  (define (literal-value e)
    (set! v e))
  
  (define (quote-value e)
    (set! v e))
  
  (define (apply-native i)
    (let ((rands (take θ i)))
      (and (contains-env? rands)
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
    (if (pair? ms)
        (begin
          (eval (car ms))
          (run-trace (cdr ms)))
        #f))
  
  (define (append-trace ms)
    (and τ (set! τ (append (reverse ms) τ))))
  
  (define (execute . ms)
    (and (is-tracing?)
         (append-trace ms))
    (run-trace ms))
  
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
            (and (not (= i 0))
                 (error "Incorrect number of args: " (lam x es) ", i = " i))
            (execute `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ)))
           ((cons x xs)
            (and (< i 0)
                 (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
            (execute `(restore-val)
                     `(alloc-var ',x))
            (loop (- i 1) xs))
           ((? symbol? x)
            (and (< i 0)
                 ((error "Incorrect number of args: " (lam x es) "case 3")))
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
      ((ev `(can-close-loop ,e . ,debug-info) κ)
       (execute `(add-continuation ,(can-close-loopk debug-info)))
       (ev e (cons (can-close-loopk debug-info) κ)))
      ((ev `(can-start-loop ,e . ,debug-info) κ)
       (execute `(add-continuation ,(can-start-loopk debug-info)))
       (ev e (cons (can-start-loopk debug-info) κ)))
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
      ((ev `(lambda ,x ,es ...) (cons φ κ))
       (execute `(create-closure ',x ',es)
                `(remove-continuation))
       (ko φ κ))
      ((ev `(let () . ,expressions)  κ)
       (eval-seq expressions κ))
      ((ev `(let ((,var ,val) . ,bds) . ,es) κ)
       (and (not (null? bds))
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
         (and (save-next-guard-id?)
              (execute `(push-guard-id! ,new-guard-id)))
         (if v
             (begin (execute `(guard-true ,new-guard-id ',(if (null? e2)
                                                              '()
                                                              (car e2)))) ;If the guard fails, the predicate was false, so e2 should be evaluated
                    (ev e1 κ))
             (begin (execute `(guard-false ,new-guard-id ',e1)) ;If the guard fails, the predicate was true, so e1 should be evaluated
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
      ((ko (seqk '()) (cons φ κ)) ;TODO No tailcall optimization!
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
  
  (define (inject e)
    (ev e `(,(haltk))))
  
  (struct env (lst) #:transparent)
  
  (define (make-new-env)
    (env '()))
  
  (define (add-var-to-env old-env var adr)
    (let ((old-lst (env-lst old-env)))
      (env (cons (cons var adr) old-lst))))
  
  (define (reset!)
    (set! ρ (make-new-env));
    (set! σ '());
    (set! θ '())
    (set! τ '())
    (set! τ-κ `(,(haltk)))
    (set! global-tracer-context (new-tracer-context)))
  
  (define (clear-trace!)
    (set! τ '()))
  
  (define (bootstrap guard-id state)
    (let ((existing-trace (get-guard-trace guard-id)))
      (output "------ BOOTSTRAP: FULL GUARD PATH: ") (output (generate-guard-trace-key)) (output " ------") (output-newline)
      (cond (existing-trace
             (output "----------- STARTING FROM GUARD ") (output guard-id) (output " -----------") (output-newline)
             (execute `(let* ((value (call/cc (lambda (k)
                                                (push-trace-frame! ,existing-trace k)
                                                (eval ,(trace-node-trace existing-trace))
                                                (ko (car τ-κ) (cdr τ-κ))))))
                         (pop-trace-frame!)
                         (let ((kk (top-continuation)))
                           (and (not (sentinel? value))
                                (remove-continuation))
                           ;(output "in bootstrap: sentinel? ") (output (sentinel? value)) (output ", value = ") (output value) (output-newline)
                           (kk (sentinel (list (unwrap-possible-sentinel value))))))))
            ((not (is-tracing?))
             (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
             (let ((old-trace-key (generate-guard-trace-key))
                   (kk (top-continuation)))
               ;(execute ;`(pop-head-executing!))
               ;         `(pop-continuation!))
               (start-tracing-after-guard! guard-id old-trace-key)
               (kk (sentinel (list state)))))
            (else
             (output "----------- CANNOT TRACE GUARD ") (output guard-id)
             (output " ; ALREADY TRACING ANOTHER LABEL -----------") (output-newline)
             (let ((kk (top-continuation)))
               ;(execute ;`(pop-head-executing!))
               ;         `(pop-continuation!))
               (kk (sentinel (list state))))))))
  
  (define (bootstrap-to-ev guard-id e)
    (bootstrap guard-id (ev e τ-κ)))
  
  (define (bootstrap-to-ko guard-id φ)
    (bootstrap guard-id (ko φ τ-κ)))
  
  (define (step* s)
    (match s
      ((ko (haltk) _)
       v)
      ((ev `(splits-control-flow) (cons φ κ))
       (execute `(remove-continuation))
       (set-tracer-context-save-next-guard-id?! global-tracer-context #t)
       (step* (ko φ κ)))
      ((ev `(merges-control-flow) (cons φ κ))
       (execute `(remove-continuation)
                `(pop-guard-id!))
       (step* (ko φ κ)))
      ((ko (can-close-loopk debug-info) (cons φ κ))
       (and (not (null? debug-info))
            (output "closing annotation: tracing loop ") (output v) (output-newline))
       (and (is-tracing-label? v)
            (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
            (set-closing-function-if-not-yet-existing! (make-stop-tracing-after-label-function))
            (stop-tracing! #f))
       (execute `(remove-continuation))
       (step* (ko φ κ)))
      ((ko (can-start-loopk debug-info) (cons φ κ))
       (and (not (null? debug-info))
            (output "opening annotation: tracing loop ") (output v) (output-newline))
       (cond ((is-tracing-label? v)
              (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
              (set-closing-function-if-not-yet-existing! (make-stop-tracing-after-label-function))
              (stop-tracing! #t)
              (start-executing-label-trace! v)
              (step* (ko (car τ-κ) (cdr τ-κ))))
             ((label-traced? v)
              (output "----------- EXECUTING TRACE -----------") (output-newline)
              (start-executing-label-trace! v)
              (step* (ko (car τ-κ) (cdr τ-κ))))
             ((and (not (is-tracing?)) (>= (get-times-label-encountered v) TRACING_THRESHOLD))
              (output "----------- STARTED TRACING -----------") (output-newline)
              (start-tracing-label! v)
              (execute `(remove-continuation))
              (let ((new-state (ko φ κ)))
                (step* new-state)))
             (else
              (execute `(remove-continuation))
              (inc-times-label-encountered! v)
              (and (is-tracing?)
                   (output "----------- ALREADY TRACING ANOTHER LABEL -----------") (output-newline))
              (let ((new-state (ko φ κ)))
                (step* new-state)))))
      (_
       (let ((new-state (step s)))
         (step* new-state)))))
  
  (define (run s)
    (reset!)
    (apply step* (sentinel-value (let ((v (call/cc (lambda (k)
                                                     (push-continuation! k)
                                                     (sentinel (list s))))))
                                   ;(display "topmost continuation") (newline)
                                   ;(display v) (newline)
                                   v))))
  
  (define (start)
    (run (inject (read)))))
