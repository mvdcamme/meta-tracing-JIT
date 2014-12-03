(module tracing-interpreter racket
  (provide (rename-out [duplicating-inject inject])
           run
           
           add-continuation
           alloc-var
           apply-native
           create-closure
           debug
           guard-false
           guard-true
           guard-same-closure
           literal-value
           lookup-var
           quote-value
           pop-head-executing!
           pop-label-executing!
           push-head-executing!
           push-label-executing!
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
           switch-to-clo-env)
  
  (require rnrs/arithmetic/bitwise-6)
  
  (define ns (make-base-namespace))
  
  (define global-e #f)
  
  (define ENABLE_OPTIMIZATIONS #f)
  (define ENABLE_OUTPUT #f)
  (define TRACING_THRESHOLD 5)
  
  (define guard-id 0)
  
  (define (inc-guard-id!)
    (let ((temp guard-id))
      (set! guard-id (+ guard-id 1))
      temp))
  
  (define (output s)
    (and ENABLE_OUTPUT
         (display s)))
  
  (define (output-newline)
    (output #\newline))
  
  (define (massoc el lst)
    (cond ((null? lst) #f)
          ((eq? el (mcar (car lst))) (car lst))
          (else (massoc el (cdr lst)))))
  
  (struct t (head tail counter) #:transparent #:mutable)
  (struct u (head counter) #:transparent #:mutable)
  
  (define (transform-input input)
    (define (tree-rec el)
      (cond ((pair? el)
             (cond ((eq? (car el) 'define)
                    (t 'define (cons (cadr el) (map tree-rec (cddr el))) '()))
                   ((eq? (car el) 'lambda)
                    (t 'lambda (cons (cadr el) (map tree-rec (cddr el))) '()))
                   ((eq? (car el) 'let*)
                    (t 'let* 
                       (let* ((bindings (cadr el))
                              (var-names (map car bindings))
                              (values (map cadr bindings)))
                         (cons (map (lambda (var value)
                                      (list var (tree-rec value)))
                                    var-names
                                    values)
                               (map tree-rec (cddr el))))
                       '()))
                   ((eq? (car el) 'quote)
                    (t 'quote (cadr el) '()))
                   ((or (eq? (car el) 'and)
                        (eq? (car el) 'apply)
                        (eq? (car el) 'begin)
                        (eq? (car el) 'can-close-loop)
                        (eq? (car el) 'can-start-loop)
                        (eq? (car el) 'cond)
                        (eq? (car el) 'if)
                        (eq? (car el) 'letrec)
                        (eq? (car el) 'or)
                        (eq? (car el) 'set!))
                    (t (car el) (map tree-rec (cdr el)) '()))
                   (else (t (tree-rec (car el)) (map tree-rec (cdr el)) '()))))
            (else (u el '()))))
    (tree-rec input))
  
  (define (s)
    (transform-input (read)))
  
  ;
  ; continuations
  ;
  
  (struct ev (e κ) #:transparent)
  (struct ko (φ κ) #:transparent)
  (struct andk (es))
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
  (struct ork (es))
  (struct randk (e es i))
  (struct ratork (i debug))
  (struct seqk (es))
  (struct setk (x))
  
  ;
  ; Random number generation
  ; Source: taken from https://github.com/SOM-st/SOM/blob/master/Examples/Benchmarks/Random.som
  ;
  
  (define random (clo (lam '(max)
                           (map transform-input '((set! seed (bitwise-and (+ (* seed 1309) 13849) 65535))
                                                  (modulo seed max))))
                      '((seed . u-seed))))
  
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
                     guard-id) #:transparent)
  
  (define (is-tracing-guard? trace-key)
    (not (eq? (trace-key-guard-id trace-key) #f)))
  
  (struct label-trace (label
                       trace
                       (children #:mutable)))
  
  (struct tracer-context (is-tracing?
                          trace-key-to-be-traced
                          label-traces
                          labels-encountered
                          labels-executing
                          heads-executing) #:transparent #:mutable)
  
  (define (new-tracer-context)
    (tracer-context #f
                    #f
                    '()
                    '()
                    '()
                    '()))
  
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
  
  (define (get-label-executing)
    (let ((labels-executing (tracer-context-labels-executing global-tracer-context)))
      (if (null? labels-executing)
          (error "Labels-executing stack is empty!")
          (car labels-executing))))
  
  (define (pop-label-executing!)
    (let ((labels-executing (tracer-context-labels-executing global-tracer-context)))
      (if (null? labels-executing)
          (error "Labels-executing stack is empty!")
          (set-tracer-context-labels-executing! global-tracer-context
                                                (cdr labels-executing)))))
  
  (define (push-label-executing! label)
    (let ((labels-executing (tracer-context-labels-executing global-tracer-context)))
      (set-tracer-context-labels-executing! global-tracer-context
                                            (cons label labels-executing))))
  
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
  
  (define (find-label-trace label)
    (define (loop label-traces)
      (cond ((null? label-traces) #f)
            ((equal? (label-trace-label (car label-traces)) label) (car label-traces))
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
                                      (cons (label-trace label transformed-trace '())
                                            (tracer-context-label-traces global-tracer-context))))
  
  (define (add-guard-trace! id trace)
    (set-label-trace-children! (get-head-executing)
                               (cons (label-trace id trace '())
                                     (label-trace-children (get-head-executing)))))
  
  (define (get-guard-trace id)
    (let ((head-executing-children (label-trace-children (get-head-executing))))
      (define (loop lst)
        (cond ((null? lst) #f)
              ((eq? (label-trace-label (car lst)) id) (car lst))
              (else (loop (cdr lst)))))
      (loop head-executing-children)))
  
  (define (start-tracing-label! label)
    (clear-trace!)
    (set-tracer-context-is-tracing?! global-tracer-context #t)
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context (trace-key label #f)))
  
  (define (start-tracing-after-guard! label guard-id)
    (clear-trace!)
    (let ((new-trace-key (trace-key label guard-id)))
      (set-tracer-context-is-tracing?! global-tracer-context #t)
      (set-tracer-context-trace-key-to-be-traced! global-tracer-context new-trace-key)))
  
  (define (start-executing-label-trace! label)
    (let* ((label-trace (get-label-trace label))
           (trace (label-trace-trace label-trace)))
      (execute `(push-label-executing! ',label)
               `(push-head-executing! ,label-trace)
               `(eval ,trace)
               `(pop-head-executing!)
               `(pop-label-executing!))
      (let ((new-state (ko (car τ-κ) (cdr τ-κ))))
        (execute `(remove-continuation))
        (step* new-state))))
  
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
    (set-tracer-context-trace-key-to-be-traced! global-tracer-context #f))
  
  (define (stop-tracing-after-guard! transformed-trace)
    (let ((label (trace-key-label (tracer-context-trace-key-to-be-traced global-tracer-context)))
          (guard-id (trace-key-guard-id (tracer-context-trace-key-to-be-traced global-tracer-context))))
      (add-guard-trace! guard-id transformed-trace)
      (stop-tracer-context-tracing!)))
  
  (define (stop-tracing-label! transformed-trace)
    (add-label-trace! (trace-key-label (tracer-context-trace-key-to-be-traced global-tracer-context)) transformed-trace)
    (stop-tracer-context-tracing!))
  
  (define (stop-tracing! loop-closed?)
    (let ((transformed-trace (if ENABLE_OPTIMIZATIONS
                                 (transform-trace (optimize-trace (reverse τ)) loop-closed?)
                                 (transform-trace (reverse τ) loop-closed?))))
      (if (is-tracing-guard? (tracer-context-trace-key-to-be-traced global-tracer-context))
          (stop-tracing-after-guard! transformed-trace)
          (stop-tracing-label! transformed-trace))))
  
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
    (/ (calculate-total-traces-length) (calculate-total-number-of-traces)))
  
  (define (calculate-duplicity)
    (define number-of-nodes 0)
    (define total-times-traced 0)
    (define (tree-rec node)
      ;(output number-of-nodes) (output-newline)
      ;(and (= number-of-nodes 139)
      ;     (= 1 1))
      (cond ((t? node) (and (> (length (t-counter node)) 0)
                            (set! number-of-nodes (+ number-of-nodes 1))
                            (set! total-times-traced (+ total-times-traced (length (t-counter node)))))
                       (tree-rec (t-head node))
                       (and (list? (t-tail node))
                            (map tree-rec (t-tail node))))
            ((u? node) (and (> (length (u-counter node)) 0)
                            (set! number-of-nodes (+ number-of-nodes 1))
                            (set! total-times-traced (+ total-times-traced (length (u-counter node))))))
            ((list? node) (map tree-rec (cdr node)))))
    (tree-rec global-e)
    (/ total-times-traced number-of-nodes))
  
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
  
  (define (save-val)
    (set! θ (cons v θ)))
  
  (define (save-vals i)
    (set! θ (append (take v i) θ))
    (set! v (drop v i)))
  
  (define (save-all-vals)
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
    (set! θ (cdr θ)))
  
  (define (restore-vals i)
    (set! v (take θ i))
    (set! θ (drop θ i)))
  
  (define (alloc-var x)
    (let ((a (gensym)))
      (set! ρ (cons (cons x a) ρ))
      (set! σ (cons (cons a v) σ))))
  
  (define (set-var x)
    (let ((a (cdr (assoc x ρ))))
      (set! σ (cons (cons a v) σ))))
  
  (define (debug)
    (= 1 1))
  
  (define (lookup-var x)
    (and (eq? x 'debug) (debug))
    (let ((binding (assoc x ρ)))
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
      ((list e)
       (ev e κ))
      ((cons e es)
       (execute `(save-env)
                `(add-continuation ,(seqk es)))
       (ev e (cons (seqk es) κ)))))
  
  (define (member-equal? el lst)
    (cond ((null? lst) #f)
          ((equal? el (car lst)) lst)
          (else (member-equal? el (cdr lst)))))
  
  (define (do-function-call i κ)
    (match v
      ((clo (lam x es) ρ)
       (execute `(switch-to-clo-env ,i))
       (let loop ((i i) (x x))
         (match x
           ('()
            (execute `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ)))
           ((cons x xs)
            (execute `(restore-val)
                     `(alloc-var ',x))
            (loop (- i 1) xs))
           ((? symbol? x)
            (execute `(restore-vals ,i)
                     `(alloc-var ',x)
                     `(add-continuation ,(applicationk (lam x es))))
            (eval-seq es (cons (applicationk (lam x es)) κ))))))
      (_
       (execute `(apply-native ,i)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))))
  
  (define (step state)
    (and (is-tracing?)
         (ev? state)
         (let ((labels (cons (tracer-context-trace-key-to-be-traced global-tracer-context)
                             (map label-trace-label (tracer-context-heads-executing global-tracer-context)))))
           (cond ((t? (ev-e state))
                  (and (not (member-equal? labels (t-counter (ev-e state))))
                       (set-t-counter! (ev-e state) (cons labels (t-counter (ev-e state))))))
                 ((u? (ev-e state))
                  (and (not (member-equal? labels (u-counter (ev-e state))))
                       (set-u-counter! (ev-e state) (cons labels (u-counter (ev-e state)))))))))
    (match state
      ((ev (t 'and `(,e . ,es) _) κ)
       (execute `(add-continuation ,(andk es)))
       (ev e (cons (andk es) κ)))
      ((ev (t 'apply `(,rator ,args) _) κ)
       (execute `(add-continuation ,(applyk rator)))
       (ev args (cons (applyk rator) κ)))
      ((ev (u (? symbol? x) _) (cons φ κ))
       (execute `(lookup-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ev (t 'begin `(,es ...) _) κ)
       (eval-seq es κ))
      ((ev (t 'can-close-loop `(,e . ,debug-info) _) κ)
       (execute `(add-continuation ,(can-close-loopk debug-info)))
       (ev e (cons (can-close-loopk debug-info) κ)))
      ((ev (t 'can-start-loop `(,e . ,debug-info) _) κ)
       (execute `(add-continuation ,(can-start-loopk debug-info)))
       (ev e (cons (can-start-loopk debug-info) κ)))
      ((ev (t 'cond `() _) (cons φ κ))
       (execute `(literal-value ())
                `(remove-continuation))
       (ko φ κ))
      ((ev (t 'cond `(,(t (u 'else _) es _)) _) κ)
       (eval-seq es κ))
      ((ev (t 'cond `(,(t pred pes _) . ,es) _) κ)
       (execute `(save-env)
                `(add-continuation ,(condk pes es)))
       (ev pred (cons (condk pes es) κ)))
      ((ev (t 'define `(,pattern . ,expressions) _) κ)
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
      ((ev (t 'if `(,e ,e1 . ,e2) _) κ)
       (execute `(save-env)
                `(add-continuation ,(ifk e1 e2)))
       (ev e (cons (ifk e1 e2) κ)))
      ((ev (t 'lambda `(,x ,es ...) _) (cons φ κ))
       (execute `(create-closure ',x ',es)
                `(remove-continuation))
       (ko φ κ))
      ((ev (t 'let* `(() . ,expressions) _) κ)
       (eval-seq expressions κ))
      ((ev (t 'let* `(((,var-name ,value) . ,other-bindings) . ,expressions) _) κ)
       (execute `(save-env)
                `(add-continuation ,(let*k var-name other-bindings expressions)))
       (ev value (cons (let*k var-name other-bindings expressions) κ)))
      ((ev (t 'letrec `(((,x ,e)) ,es ...) _) κ)
       (execute `(literal-value undefined)
                `(alloc-var ',x)
                `(save-env)
                `(add-continuation ,(letk x es)))
       (ev e (cons (letk x es) κ)))
      ((ev (t 'or `(,e . ,es) _) κ)
       (execute `(add-continuation ,(ork es)))
       (ev e (cons (ork es) κ)))
      ((ev (t 'quote e _) (cons φ κ))
       (execute `(quote-value ',e)
                `(remove-continuation))
       (ko φ κ))
      ((ev (t 'set! `(,(u x _) ,e) _) κ)
       (execute `(save-env)
                `(add-continuation ,(setk x)))
       (ev e (cons (setk x) κ)))
      ((ev (t rator `() _) κ)
       (execute `(save-env)
                `(add-continuation ,(ratork 0 'regular-nulary)))
       (ev rator (cons (ratork 0 'regular-nulary) κ)))
      ((ev (t rator rands _) κ)
       (execute `(save-env))
       (let ((rrands (reverse rands)))
         (execute `(add-continuation ,(randk rator (cdr rrands) 1)))
         (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
      ((ev (u e _) (cons φ κ))
       (execute `(literal-value ,e)
                `(remove-continuation))
       (ko φ κ))
      ((ko (andk '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (andk es) κ)
       (if v
           (ev (t 'and es '()) κ)
           (begin (execute `(remove-continuation)
                           `(literal-value #f))
                  (ko (car κ) (cdr κ)))))
      ((ko (applicationk debug) κ)
       (execute `(restore-env)
                `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (applyk rator) κ)
       (let ((i (length v)))
         (execute `(save-all-vals)
                  `(save-env)
                  `(add-continuation ,(ratork i 'apply)))
         (ev rator (cons (ratork i 'apply) κ))))
      ((ko (closure-guard-failedk i) κ)
       (do-function-call i κ))
      ((ko (condk pes es) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',(t 'cond es '())))
                  (eval-seq pes κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',(t 'begin pes '())))
                  (ev (t 'cond es '()) κ))))
      ((ko (definevk x) (cons φ κ))
       (execute `(restore-env)
                `(alloc-var ',x)
                `(remove-continuation))
       (ko φ κ))
      ((ko (haltk) _)
       #f)
      ((ko (ifk e1 e2) κ)
       (execute `(restore-env))
       (if v
           (begin (execute `(guard-true ,(inc-guard-id!) ',(if (null? e2)
                                                               '()
                                                               (car e2)))) ;If the guard fails, the predicate was false, so e2 should be evaluated
                  (ev e1 κ))
           (begin (execute `(guard-false ,(inc-guard-id!) ',e1)) ;If the guard fails, the predicate was true, so e1 should be evaluated
                  (if (null? e2)
                      (begin (execute `(remove-continuation)
                                      `(literal-value '()))
                             (ko (car κ) (cdr κ)))
                      (ev (car e2) κ)))))
      ((ko (letk x es) κ)
       (execute `(restore-env)
                `(set-var ',x))
       (eval-seq es κ))
      ((ko (let*k x bds es) κ)
       (execute `(restore-env)
                `(alloc-var ',x)
                `(set-var ',x))
       (ev (t 'let* `(,bds ,@es) '()) κ))
      ((ko (ork '()) κ)
       (execute `(remove-continuation))
       (ko (car κ) (cdr κ)))
      ((ko (ork es) κ)
       (if v
           (begin (execute `(remove-continuation))
                  (ko (car κ) (cdr κ)))
           (ev (t 'or es '()) κ)))
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
  
  (define (duplicating-inject e)
    (let ((transformed-e (transform-input e)))
      (output "INPUT TRANSFORMED") (output-newline)
      (set! global-e transformed-e)
      (ev transformed-e `(,(haltk)))))
  
  (define (inject e)
    (ev e `(,(haltk))))
  
  (define (reset!)
    (set! ρ '((random . u-random)));
    (set! σ `((u-seed . 74755)
              (u-random . ,random)));
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
             (pop-label-executing!)
             (let ((new-state (ko (car τ-κ) (cdr τ-κ))))
               (execute `(remove-continuation))
               (global-continuation (list new-state))))
            ((not (is-tracing?))
             (output "----------- STARTED TRACING GUARD ") (output guard-id) (output " -----------") (output-newline)
             (start-tracing-after-guard! (get-label-executing) guard-id)
             (pop-label-executing!)
             (global-continuation (list (ev e τ-κ))))
            (else
             (output "----------- CANNOT TRACE GUARD ") (output guard-id)
             (output " ; ALREADY TRACING ANOTHER LABEL -----------") (output-newline)
             (global-continuation (list (ev e τ-κ))))))) ;step* called with the correct arguments
  
  (define (bootstrap-from-continuation guard-id φ)
    (start-tracing-after-guard! (get-label-executing) guard-id)
    (pop-label-executing!)
    (global-continuation (list (ko φ τ-κ))))
  
  (define (step* s)
    (match s
      ((ko (haltk) _)
       v)
      ((ev (t (u 'merges-control-flow _) `() _) (cons φ κ))
       (execute `(remove-continuation))
       ;TODO implementation
       (step* (ko φ κ)))
      ((ko (can-close-loopk debug-info) (cons φ κ))
       (and (not (null? debug-info))
            (output "closing annotation: tracing loop ") (output v) (output-newline))
       (and (is-tracing-label? v)
            (output "----------- CLOSING ANNOTATION FOUND; TRACING FINISHED -----------") (output-newline)
            (stop-tracing! #f))
       (execute `(remove-continuation))
       (step* (ko φ κ)))
      ((ko (can-start-loopk debug-info) (cons φ κ))
       (and (not (null? debug-info))
            (output "opening annotation: tracing loop ") (output v) (output-newline))
       (cond ((is-tracing-label? v)
              (output "-----------TRACING FINISHED; EXECUTING TRACE -----------") (output-newline)
              (stop-tracing! (if (is-tracing-guard? (tracer-context-trace-key-to-be-traced global-tracer-context))
                                 #f
                                 #t))
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
    (run (duplicating-inject (read)))))
