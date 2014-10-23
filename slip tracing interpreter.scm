#lang racket

;; Slippy: lambda letrec if set! begin quote

(define ENABLE_OPTIMIZATIONS #t)

(define ns (make-base-namespace))

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
(struct applicationk () #:transparent)
(struct applyk (rator) #:transparent)
(struct can-start-loopk (debug-info) #:transparent)
(struct clo (λ ρ) #:transparent)
(struct closure-guard-validatedk (i))
(struct condk (pes es))
(struct definevk (x)) ;define variable
(struct haltk ())
(struct ifk (e1 e2))
(struct lam (x es) #:transparent)
(struct letk (x es))
(struct let*k (x bds es))
(struct ork (es))
(struct randk (e es i))
(struct ratork (i))
(struct seqk (es))
(struct setk (x))

(define (clo-equal? clo1 clo2)
  (and (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
       (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2)))))

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

(struct tracer-context (is-tracing? expression-to-be-traced expressions-encountered expressions-already-traced) #:transparent)

(define (new-tracer-context)
  (tracer-context #f #f '() '()))

(define is-tracing? tracer-context-is-tracing?)

(define (is-tracing-expression? tracer-context expression)
  (eq? (tracer-context-expression-to-be-traced tracer-context) expression))

(define (expression-encountered? tracer-context expression)
  (member expression (tracer-context-expressions-encountered tracer-context)))

(define (add-expression-encountered old-tracer-context expression)
  (struct-copy tracer-context old-tracer-context
               (expressions-encountered (cons expression (tracer-context-expressions-encountered old-tracer-context)))))

(define (expression-traced? tracer-context expression)
  (assoc expression (tracer-context-expressions-already-traced tracer-context)))

(define (expression-trace tracer-context expression)
  (cdr (assoc expression (tracer-context-expressions-already-traced tracer-context))))

(define (start-tracing-expression old-tracer-context expression)
  (struct-copy tracer-context old-tracer-context (is-tracing? #t) (expression-to-be-traced expression)))

;
; Transform trace
;

(define (transform-trace trace)
  `(letrec ((loop ,(append '(lambda ()) trace '((loop)))))
     (loop)))

;
; Optimize trace
;

(define (changes-env? instruction)
  (or (eq? instruction 'guard-false)
      (eq? instruction 'guard-true)
      (eq? instruction 'guard-same-closure)
      (eq? instruction 'set-env)
      (eq? instruction 'alloc-var)))

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

(define (stop-tracing old-tracer-context)
  (if ENABLE_OPTIMIZATIONS
      (set! τ (transform-trace (optimize-trace (reverse τ))))
      (set! τ (transform-trace (reverse τ))))
  (struct-copy tracer-context old-tracer-context
               (expressions-already-traced
                (cons (cons (tracer-context-expression-to-be-traced old-tracer-context) τ)
                      (tracer-context-expressions-already-traced old-tracer-context))) ;TODO assumes that the expression hasn't been traced already
               (is-tracing? #f)
               (expression-to-be-traced #f)))

(define global-tracer-context #f)

;
;evaluation
;

(define (guard-false e)
  (if v
      (begin (display "Guard-false failed") (newline) (bootstrap e))
      (begin (display "Guard passed") (newline))))

(define (guard-true e)
  (if v
      (begin (display "Guard passed") (newline))
      (begin (display "Guard-true failed") (newline) (bootstrap e))))

(define (guard-same-closure clo i)
  (and (not (clo-equal? v clo))
       (display "Closure guard failed, expected: ") (display clo) (display ", evaluated: ") (display v) (newline)
       (bootstrap-from-continuation (closure-guard-validatedk i))))

(define (save-val)
  (set! θ (cons v θ)))

(define (save-vals i)
  (set! θ (append (take v i) θ))
  (set! v (drop v i)))

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

(define (lookup-var x)
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

(define (run-trace ms)
  (if (pair? ms)
      (begin
        (eval (car ms))
        (run-trace (cdr ms)))
      #f))

(define (append-trace ms)
  (and τ (set! τ (append (reverse ms) τ))))

(define (execute . ms)
  (and (is-tracing? global-tracer-context)
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
    ((ev `(let* () . ,expressions) κ)
     (eval-seq expressions κ))
    ((ev `(let* ((,var-name ,value) . ,other-bindings) . ,expressions) κ)
     (execute `(save-env)
              `(add-continuation ,(let*k var-name other-bindings expressions)))
     (ev value (cons (let*k var-name other-bindings expressions) κ)))
    ((ev `(letrec ((,x ,e)) ,es ...) κ)
     (execute `(literal-value undefined)
              `(alloc-var ',x)
              `(save-env)
              `(add-continuation ,(letk x es)))
     (ev e (cons (letk x es) κ)))
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
              `(add-continuation ,(ratork 0)))
     (ev rator (cons (ratork 0) κ)))
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
    ((ko (andk es) κ)
     (if v
         (ev `(and ,@es) κ)
         (begin (execute `(remove-continuation)
                         `(literal-value #f))
                (ko (car κ) (cdr κ)))))
    ((ko (applicationk) κ)
     (execute `(restore-env)
              `(remove-continuation))
     (ko (car κ) (cdr κ)))
    ((ko (applyk rator) κ)
     (let ((i (length v)))
       (execute `(save-vals ,i)
                `(save-env)
                `(add-continuation ,(ratork i)))
       (ev rator (cons (ratork i) κ))))
    ((ko (closure-guard-validatedk i) κ)
     (match v
       ((clo (lam x es) ρ)
        (execute `(restore-vals ,i)
                 `(save-env)
                 `(save-vals ,i)
                 `(set-env (clo-ρ ,v)))
        (let loop ((i i) (x x))
          (match x
            ('()
             (execute `(add-continuation ,(applicationk)))
             (eval-seq es (cons (applicationk) κ)))
            ((cons x xs)
             (execute `(restore-val)
                      `(alloc-var ',x))
             (loop (- i 1) xs))
            ((? symbol? x)
             (execute `(restore-vals ,i)
                      `(alloc-var ',x)
                      `(add-continuation ,(applicationk)))
             (eval-seq es (cons (applicationk) κ))))))))
    ((ko (condk pes es) κ)
     (execute `(restore-env))
     (if v
         (begin (execute `(guard-true ',`(cond ,@es)))
                (eval-seq pes κ))
         (begin (execute `(guard-false ',`(begin ,@pes)))
                (ev `(cond ,@es) κ))))
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
         (begin (execute `(guard-true ',e2)) ;If the guard fails, the predicate was false, so e2 should be evaluated
                (ev e1 κ))
         (begin (execute `(guard-false ',e1)) ;If the guard fails, the predicate was true, so e1 should be evaluated
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
     (ev `(let* ,bds ,@es) κ))
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
              `(add-continuation ,(ratork i)))
     (ev rator (cons (ratork i) κ)))
    ((ko (randk rator rands i) κ)
     (execute `(restore-env)
              `(save-val)
              `(save-env)
              `(add-continuation ,(randk rator (cdr rands) (+ i 1))))
     (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
    ((ko (ratork i) κ)
     (execute `(restore-env))
     (match v
       ((clo (lam x es) ρ)
        (execute `(guard-same-closure ,v ,i)) ;TODO τ-κ does not need to be changed?
        (ko (closure-guard-validatedk i) κ))
       (_
        (execute `(apply-native ,i)
                 `(remove-continuation))
        (ko (car κ) (cdr κ)))))
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

(define (reset!)
  (set! ρ '());
  (set! σ '());
  (set! θ '())
  (set! τ '())
  (set! τ-κ `(,(haltk)))
  (set! global-tracer-context (new-tracer-context)))

(define (clear-trace!)
  (set! τ '()))

(define (bootstrap e)
  (global-continuation (list (ev e τ-κ)))) ;step* called with the correct arguments

(define (bootstrap-from-continuation φ)
  (global-continuation (list (ko φ τ-κ))))

(define (step* s)
  (match s
    ((ko (haltk) _)
     v)
    ((ko (can-start-loopk debug-info) (cons φ κ))
     (and (not (null? debug-info))
          (display "tracing loop ") (display (car debug-info)) (newline))
     (cond ((expression-traced? global-tracer-context v)
            (display "----------- EXECUTING TRACE -----------") (newline)
            (let ((trace (expression-trace global-tracer-context v)))
              (eval trace)))
           ((is-tracing-expression? global-tracer-context v)
            (display "-----------TRACING FINISHED; EXECUTING TRACE -----------") (newline)
            (set! global-tracer-context (stop-tracing global-tracer-context))
            (let ((trace (expression-trace global-tracer-context v)))
              (eval trace)))
           ((and (not (is-tracing? global-tracer-context)) (expression-encountered? global-tracer-context v))
            (display "----------- STARTED TRACING -----------") (newline)
            (clear-trace!)
            (set! global-tracer-context (start-tracing-expression global-tracer-context v))
            (let ((new-state (ko φ κ)))
              (execute `(remove-continuation))
              (step* new-state)))
           ((not (expression-encountered? global-tracer-context v))
            (set! global-tracer-context (add-expression-encountered global-tracer-context v))
            (let ((new-state (ko φ κ)))
              (execute `(remove-continuation))
              (step* new-state)))
           (else
            (display "----------- ALREADY TRACING ANOTHER EXPRESSION -----------") (newline)
            (let ((new-state (step (ko φ κ))))
              (execute `(remove-continuation))
              (step* new-state)))))
    (_
     (let ((new-state (step s)))
       (step* new-state)))))

(define (run s)
  (reset!)
  (apply step* (call/cc (lambda (k) (set! global-continuation k) (list s)))))

(define (start)
  (run (inject (read))))