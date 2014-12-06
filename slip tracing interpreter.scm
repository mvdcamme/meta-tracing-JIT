(module tracing-interpreter racket
  (provide inject
           run
           
           ;;trace instructions
           add-continuation
           alloc-var
           apply-native
           create-closure
           debug
           guard-false
           guard-true
           guard-same-closure
           guard-same-nr-of-args
           literal-value
           lookup-var
           quote-value
           pop-guard-id!
           pop-head-executing!
           push-guard-id!
           push-head-executing!
           remove-continuation
           reset-head-executing!
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
           
           ;;metrics
           calculate-average-trace-length
           calculate-total-number-of-traces
           calculate-total-traces-length)
           
  
  (require "dictionary.scm")
  (require "stack.scm")
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define ENABLE_OUTPUT #f)
  (define TRACING_THRESHOLD 5)
  
  (define guard-id 0)
  
  (define (inc-guard-id!)
    (let ((temp guard-id))
      (set! guard-id (+ guard-id 1))
      temp))
  
  (define ns (make-base-namespace))
  
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
  (struct randk (e es i))
  (struct ratork (i debug))
  (struct seqk (es))
  (struct setk (x))
  
  (define (clo-equal? clo1 clo2)
    (or (eq? clo1 clo2)
        (and (clo? clo1)
             (clo? clo2)
             (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
             (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2))))))
  
  (define ρ #f) ; env
  (define σ #f) ; store
  (define θ #f) ; non-kont stack
  (define v #f) ; value
  (define τ #f) ; trace
  
  (define τ-κ #f) ;continuation stack
  
  (define global-continuation #f) ;This continuation should be called when the interpreter is being bootstrapped
  
  ;
  ;tracing
  ;
  
  (struct trace-key (label
                     guard-ids) #:transparent)
  
  (define (is-tracing-guard? trace-key)
    (not (eq? (trace-key-guard-ids trace-key) '())))
  
  (struct label-trace (label
                       trace
                       (children #:mutable)))
  
  (define (make-label-trace label trace)
    (label-trace label trace '()))
  
  (struct tracer-context (is-tracing?
                          trace-key-to-be-traced
                          save-next-guard-id?
                          label-traces
                          labels-encountered
                          heads-executing
                          guards-id-stack
                          closing-function) #:transparent #:mutable)
  
  (define (new-tracer-context)
    (tracer-context #f
                    #f
                    #f
                    '()
                    '()
                    '()
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
  
  (define (pop-head-executing!)
    (let ((heads-executing (tracer-context-heads-executing global-tracer-context)))
      (if (null? heads-executing)
          (error "Heads-executing stack is empty!")
          (set-tracer-context-heads-executing! global-tracer-context
                                               (cdr heads-executing)))))
  
  (define (push-head-executing! label-trace)
    (let ((heads-executing (tracer-context-heads-executing global-tracer-context)))
      (set-tracer-context-heads-executing! global-tracer-context
                                           (cons label-trace heads-executing))))
  
  (define (reset-head-executing!)
    (set-tracer-context-heads-executing! global-tracer-context '()))
  
  (define (find-label-trace label)
    (define (loop label-traces)
      (cond ((null? label-traces) #f)
            ((equal? (label-trace-label (car label-traces)) label) (car label-traces)) ;TODO verander equal? naar eq?
            (else (loop (cdr label-traces)))))
    (loop (tracer-context-label-traces global-tracer-context)))
  
  (define (get-label-trace label)
    (let ((label-trace-found (find-label-trace label)))
      (if label-trace-found
          label-trace-found
          (error "Label was not found in global-tracer-context: " label))))
  
  (define (label-traced? label)
    (not (eq? (find-label-trace label) #f)))
  
  (define (add-label-trace! label transformed-trace)
    (set-tracer-context-label-traces! global-tracer-context
                                      (cons (make-label-trace label transformed-trace)
                                            (tracer-context-label-traces global-tracer-context))))
  
  ;guard-ids should go from the top of the tree to the bottom
  (define (find-guard-trace label guard-ids)
    (let ((first-label-trace (get-label-trace label)))
      (define (find-next-node-in-path label-trace guard-id)
        (define (loop children)
          (cond ((null? children) (error "Trace-key was not found: " (trace-key label guard-ids)))
                ((eq? (label-trace-label (car children)) guard-id) (car children))
                (else (loop (cdr children)))))
        (loop (label-trace-children label-trace)))
      (define (follow-path label-trace guard-ids)
        (if (null? (cdr guard-ids))
            label-trace
            (follow-path (find-next-node-in-path label-trace (car guard-ids)) (cdr guard-ids))))
      (follow-path first-label-trace guard-ids)))
  
  (define (add-guard-trace! label guard-ids trace)
    (let ((parent-label-trace (find-guard-trace label guard-ids))
          (new-guard-id (last guard-ids)))
      (set-label-trace-children! parent-label-trace
                                 (cons (make-label-trace new-guard-id trace)
                                       (label-trace-children parent-label-trace)))))
  
  (define (get-guard-trace guard-id)
    (let ((head-executing-children (label-trace-children (get-head-executing))))
      (define (loop lst)
        (cond ((null? lst) #f)
              ((eq? (label-trace-label (car lst)) guard-id) (car lst))
              (else (loop (cdr lst)))))
      (loop head-executing-children)))
  
  (define (start-tracing-label! label)
    (clear-trace!)
    (set-tracer-context-is-tracing?! global-tracer-context #t)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context (trace-key label '())))
  
  (define (generate-guard-trace-key)
    (let* ((list (reverse (tracer-context-heads-executing global-tracer-context)))
           (top-label (label-trace-label (car list)))
           (guards (cdr list))
           (guard-ids-path '()))
      (for-each (lambda (guard-trace)
                  (set! guard-ids-path (cons (label-trace-label guard-trace) guard-ids-path)))
                guards)
      (trace-key top-label guard-ids-path)))
  
  (define (start-tracing-after-guard! guard-id old-trace-key)
    (clear-trace!)
    (set-tracer-context-closing-function! global-tracer-context (make-stop-tracing-after-guard-function))
    (set-tracer-context-is-tracing?! global-tracer-context #t)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context (trace-key (trace-key-label old-trace-key)
                                                                                 (cons guard-id (trace-key-guard-ids old-trace-key)))))
  
  (define (start-executing-label-trace! label)
    (let* ((label-trace (get-label-trace label))
           (trace (label-trace-trace label-trace)))
      (execute `(push-head-executing! ,label-trace)
               `(eval ,trace)
               `(pop-head-executing!))
      (let ((new-state (ko (car τ-κ) (cdr τ-κ))))
        (execute `(remove-continuation))
        (step* new-state))))
  
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
  
  (define (transform-and-optimize-trace trace loop-closed?)
    (if ENABLE_OPTIMIZATIONS
        (transform-trace (optimize-trace trace) loop-closed?)
        (transform-trace trace loop-closed?)))
  
  (define (make-stop-tracing-after-label-function looping?)
    (define (stop-tracing-label! trace)
      (let ((transformed-trace (transform-and-optimize-trace trace looping?)))
        (add-label-trace! (trace-key-label (tracer-context-trace-key-to-be-traced global-tracer-context)) transformed-trace)))
    stop-tracing-label!)
  
  (define (make-stop-tracing-after-guard-function)
    (define (stop-tracing-after-guard! trace)
      (let* ((transformed-trace (transform-and-optimize-trace trace #f))
             (trace-key (tracer-context-trace-key-to-be-traced global-tracer-context))
             (label (trace-key-label trace-key))
             (guard-ids (trace-key-guard-ids trace-key)))
        (add-guard-trace! label (reverse guard-ids) transformed-trace)))
    stop-tracing-after-guard!)
  
  (define (stop-tracing!)
    (let ((stop-tracing-function (tracer-context-closing-function global-tracer-context)))
      (stop-tracing-function (reverse τ))
      (stop-tracer-context-tracing!)))
  
  (define global-tracer-context #f)
  
  (define (calculate-total-number-of-traces)
    (define sum 0)
    (define (tree-rec lst)
      (for-each (lambda (child)
                  (set! sum (+ sum 1))
                  (tree-rec (label-trace-children child)))
                lst))
    (for-each (lambda (global-label-traces)
                (set! sum (+ sum 1))
                (tree-rec (label-trace-children global-label-traces)))
              (tracer-context-label-traces global-tracer-context))
    sum)
  
  (define (calculate-total-traces-length)
    (define sum 0)
    (define (tree-rec lst)
      (for-each (lambda (child)
                  (set! sum (+ sum (length (cddadr (caadr (label-trace-trace child))))))
                  (tree-rec (label-trace-children child)))
                lst))
    (for-each (lambda (global-label-traces)
                (set! sum (+ sum (length (cddadr (caadr (label-trace-trace global-label-traces))))))
                (tree-rec (label-trace-children global-label-traces)))
              (tracer-context-label-traces global-tracer-context))
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
        (begin (output "Guard-false failed") (output-newline) (bootstrap guard-id e))
        (begin (output "Guard passed") (output-newline))))
  
  (define (guard-true guard-id e)
    (if v
        (begin (output "Guard passed") (output-newline))
        (begin (output "Guard-true failed") (output-newline) (bootstrap guard-id e))))
  
  (define (guard-same-closure clo i guard-id)
    (and (not (clo-equal? v clo))
         (output "Closure guard failed, expected: ") (output clo) (output ", evaluated: ") (output v) (output-newline)
         (bootstrap-from-continuation guard-id (closure-guard-failedk i))))
  
  (define (guard-same-nr-of-args i rator guard-id)
    (let ((current-i (length v)))
      (and (not (= i current-i))
           (output "Argument guard failed, expected: ") (output i) (output ", evaluated: ") (output current-i) (output-newline)
           (bootstrap-from-continuation guard-id (apply-failedk rator current-i)))))
  
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
  
  (define (bootstrap guard-id e)
    (let ((existing-trace (get-guard-trace guard-id)))
      (cond (existing-trace
             (output "----------- STARTING FROM GUARD ") (output guard-id) (output " -----------") (output-newline)
             (execute `(push-head-executing! ,existing-trace)
                      `(eval ,(label-trace-trace existing-trace))
                      `(pop-head-executing!))
             (let ((new-state (ko (car τ-κ) (cdr τ-κ))))
               (execute `(remove-continuation)
                        `(pop-head-executing!))
               (global-continuation (list new-state))))
            ((not (is-tracing?))
             (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
             (let ((old-trace-key (generate-guard-trace-key)))
               (execute `(pop-head-executing!))
               (start-tracing-after-guard! guard-id old-trace-key)
               (global-continuation (list (ev e τ-κ)))))
            (else
             (output "----------- CANNOT TRACE GUARD ") (output guard-id)
             (output " ; ALREADY TRACING ANOTHER LABEL -----------") (output-newline)
             (execute `(pop-head-executing!))
             (global-continuation (list (ev e τ-κ))))))) ;step* called with the correct arguments
  
  (define (bootstrap-from-continuation guard-id φ)
    (let ((old-trace-key (generate-guard-trace-key)))
      (start-tracing-after-guard! guard-id old-trace-key)
      ;(pop-head-executing!)
      (global-continuation (list (ko φ τ-κ)))))
  
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
            (set-closing-function-if-not-yet-existing! (make-stop-tracing-after-label-function #f))
            (stop-tracing!))
       (execute `(remove-continuation))
       (step* (ko φ κ)))
      ((ko (can-start-loopk debug-info) (cons φ κ))
       (and (not (null? debug-info))
            (output "opening annotation: tracing loop ") (output v) (output-newline))
       (cond ((is-tracing-label? v)
              (output "----------- TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
              (set-closing-function-if-not-yet-existing! (make-stop-tracing-after-label-function #t))
              (stop-tracing!)
              (start-executing-label-trace! v))
             ((label-traced? v)
              (output "----------- EXECUTING TRACE -----------") (output-newline)
              (start-executing-label-trace! v))
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
    (apply step* (call/cc (lambda (k) (set! global-continuation k) (list s)))))
  
  (define (start)
    (run (inject (read)))))
