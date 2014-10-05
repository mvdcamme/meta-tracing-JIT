#lang racket

;(begin (define (fac x) (if (< x 2) 1 (* x (fac (- x 1))))) (fac 5))

(define (print s)
  (display s)
  (newline))

(define ns (make-base-namespace))
(struct ev (e ρ σ κ) #:transparent) ;state: (expression environment store list-of-continuations)
(struct ko (φ v ρ σ κ) #:transparent) ;continuation: (current-continuation value store list-of-continuations)
(struct ap (v vs ρ σ κ) #:transparent) ;application: (operator values environment store continuation)
(struct condk (pred-expressions expressions ρ))
(struct definevk (x ρ)) ;define variable
(struct haltk ()) ;halting continuation
(struct ifk (e1 e2 ρ)) ;if continuation
(struct letk (a es ρ)) ;let continuation
(struct let*k (var-name bindings expressions ρ)) ;let* continuation
(struct can-start-loopk (ρ))
(struct randk (xs vs ρ))
(struct seqk (es ρ)) ;sequence continuation
(struct setk (x ρ)) ;set! continuation
(struct clo (λ ρ)) ;closure
(struct lam (x es)) ;lambda

;
;tracing
;

(define global-tracer-context #f) ;TODO debugging

(struct tracer-context (is-tracing? expression-to-be-traced expressions-already-traced trace trace-transitions) #:transparent)

(struct def-var (var-name symbol)) ;define a variable
(struct assign-var (symbol value)) ;assign a value to the symbol
(struct set-env (new-env)) ;set the environment
(struct set-store (new-store)) ;set the store
(struct set-env-store (new-env new-store)) ;set the environment and the store
(struct apply-nat-fun (native-function n)) ;apply a native function to the first n values from the list of saved values
(struct put-val (val)) ;save the value
(struct put-var-lookup (var-name)) ;lookup the variable and save it
(struct rem-val ()) ;remove the first saved value

(define (new-tracer-context)
    (tracer-context #f #f '() '() '()))

(define is-tracing? tracer-context-is-tracing?)
  
(define (is-tracing-expression? tracer-context expression)
  (eq? (tracer-context-expression-to-be-traced tracer-context) expression))

(define (start-tracing-expression old-tracer-context expression)
  (struct-copy tracer-context old-tracer-context (is-tracing? #t) (expression-to-be-traced expression)))

(define (stop-tracing old-tracer-context)
  (struct-copy tracer-context old-tracer-context
               (expressions-already-traced (cons (cons (tracer-context-expression-to-be-traced old-tracer-context) (tracer-context-trace old-tracer-context))
                                                 (tracer-context-expressions-already-traced old-tracer-context))) ;TODO assumes that the expression hasn't been traced already
               (is-tracing? #f)
               (expression-to-be-traced #f)
               (trace '())))

(define (expression-traced? tracer-context expression)
  (assoc expression (tracer-context-expressions-already-traced tracer-context)))

(define (add-to-trace old-tracer-context expression)
  (struct-copy tracer-context old-tracer-context (trace (append (tracer-context-trace old-tracer-context) (list expression)))))

(define (add-trace-transition old-tracer-context transition)
  (struct-copy tracer-context old-tracer-context (trace-transitions (append (tracer-context-trace-transitions old-tracer-context) (list transition)))))

;(define (add-expression-traced old-tracer-context expression) TODO redundant?
 ; (struct-copy tracer-context old-tracer-context (expressions-already-traced (cons expression (vector-ref tracer-context 2)))))

;
;evaluation
;

(struct evaluated-expression (expression tracer-context))

(struct state-tracer-context (state tracer-context))

(define clo-apply (clo (lam 'operands '(apply (car operands) (cdr operands))) '()))

(define (eval-seq es ρ σ κ)
  (match es
    ((list e) (ev e ρ σ κ))
    ((cons e es) (ev e ρ σ (cons (seqk es ρ) κ)))))

(define (step state tracer-context)
  (state-tracer-context
   (match state
    ((ev (and x (? symbol?)) ρ σ (cons φ κ))
     (set! tracer-context (add-trace-transition tracer-context (put-var-lookup x)))
     (ko φ (match (assoc x ρ)
             ((cons _ a) (cdr (assoc a σ)))
             (_ (eval x ns))) ρ σ κ)) ;symbol wasn't found in environment -> check in Racket namespace
    ((ev `(begin ,es ...) ρ σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ σ)))
     (eval-seq es ρ σ κ))
    ((ev `(cond ()) ρ σ (cons φ κ))
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ σ)))
     (set! tracer-context (add-trace-transition tracer-context (put-val '())))
     (ko φ '() ρ σ κ))
    ((ev `(cond (else . ,expressions)) ρ σ κ)
     (eval-seq expressions ρ σ κ))
    ((ev `(cond (,pred . ,pred-expressions) . ,expressions) ρ σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ σ)))
     (ev pred ρ σ (cons (condk pred-expressions expressions ρ) κ)))
    ((ev `(define ,pattern . ,expressions) ρ σ (cons φ κ))
     (if (symbol? pattern)
          (let* ((fresh (gensym))
                 (ρ* (cons (cons pattern fresh) ρ)))
            (set! tracer-context (add-trace-transition tracer-context (def-var pattern fresh)))
            (ev (car expressions) ρ σ (cons (definevk fresh ρ*) (cons φ κ)))) ;TODO find a better solution for match of (cons φ κ)?
          (let* ((fresh (gensym))
                 (ρ* (cons (cons (car pattern) fresh) ρ))
                 (procedure (clo (lam (cdr pattern) expressions) ρ*))
                 (σ* (cons (cons fresh procedure) σ)))
            (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ σ)))
            (set! tracer-context (add-trace-transition tracer-context (put-val procedure)))
            (ko φ procedure ρ* σ* κ))))
    ((ev `(lambda ,x ,es ...) ρ σ (cons φ κ))
     (set! tracer-context (add-trace-transition tracer-context (put-val (clo (lam x es) ρ))))
     (ko φ (clo (lam x es) ρ) ρ σ κ))
    ((ev `(let* () . ,expressions) ρ σ κ)
     (eval-seq expressions ρ σ κ))
    ((ev `(let* ((,var-name ,value) . ,other-bindings) . ,expressions) ρ σ κ)
     (ev value ρ σ (cons (let*k var-name other-bindings expressions ρ) κ)))
    ((ev `(if ,e ,e1 ,e2) ρ σ κ)
     (ev e ρ σ (cons (ifk e1 e2 ρ) κ)))
    ((ev `(letrec ((,x ,e)) ,es ...) ρ σ κ)
     (let* ((fresh (gensym))
            (ρ* (cons (cons x fresh) ρ)))
       (set! tracer-context (add-trace-transition tracer-context (def-var x fresh)))
       (ev e ρ* σ (cons (letk fresh es ρ*) κ))))
    ((ev `(quote ,e) ρ σ (cons φ κ))
     (set! tracer-context (add-trace-transition tracer-context (put-val e)))
     (ko φ e ρ σ κ))
    ((ev `(set! ,x ,e) ρ σ κ)
     (ev e ρ σ (cons (setk x ρ) κ)))
    ((ev `(,rator . ,rands) ρ σ κ)
     (ev rator ρ σ (cons (randk rands '() ρ) κ)))
    ((ev e ρ σ (cons φ κ)) ;literal
     (set! tracer-context (add-trace-transition tracer-context (put-val e)))
     (ko φ e ρ σ κ))
    ((ko (condk pred-expressions expressions ρ) pred-value ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (rem-val)))
     (if pred-value
         (eval-seq pred-expressions ρ σ κ)
         (ev `(cond ,@expressions) ρ σ κ)))
     ((ko (definevk x ρ*) v ρ σ (cons φ κ))
      (set! tracer-context (add-trace-transition tracer-context (assign-var x v)))
      (set! tracer-context (add-trace-transition tracer-context (put-val v)))
      (let ((σ* (cons (cons x v) σ)))
        (ko φ v ρ* σ* κ)))
    ((ko (letk a es ρ) v ρ σ κ)
     (set! tracer-context (add-trace-transition tracer-context (assign-var a v)))
     (let ((σ* (cons (cons a v) σ)))
       (eval-seq es ρ σ* κ)))
    ((ko (let*k var-name other-bindings expressions ρ) value ρ* σ κ)
     (let* ((fresh (gensym))
            (ρ* (cons (cons var-name fresh) ρ))
            (σ* (cons (cons fresh value) σ)))
       (set! tracer-context (add-trace-transition tracer-context (def-var var-name fresh)))
       (set! tracer-context (add-trace-transition tracer-context (assign-var fresh value)))
       (ev `(let* ,other-bindings ,@expressions) ρ* σ* κ)))
    ((ko (setk x ρ) v ρ σ (cons φ κ))
     (match (assoc x ρ)
       (set! tracer-context (add-trace-transition tracer-context (assign-var v)))
       ((cons name a) (ko φ v ρ (cons (cons a v) σ) κ))))
    ((ko (randk '() vs ρ) v ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ σ)))
     (let ((vs (reverse (cons v vs))))
       (ap (car vs) (cdr vs) ρ σ κ)))
    ((ap (clo (lam x es) ρ*) rands ρ σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env ρ*)))
     (let loop ((x x) (rands rands) (ρ ρ*) (σ σ))
       (match x
         ('() (eval-seq es ρ σ κ))
         ((cons x xs)
          (let ((fresh (gensym)))
            (set! tracer-context (add-trace-transition tracer-context (def-var x fresh)))
            (set! tracer-context (add-trace-transition tracer-context (assign-var fresh (car rands))))
            (set! tracer-context (add-trace-transition tracer-context (rem-val)))
            (loop xs (cdr rands)
                  (cons (cons x fresh) ρ)
                  (cons (cons fresh (car rands)) σ))))
         ((and x (? symbol?))
          (let ((fresh (gensym)))
            (set! tracer-context (add-trace-transition tracer-context (def-var x fresh)))
            (set! tracer-context (add-trace-transition tracer-context (assign-var fresh rands)))
            (eval-seq es
                      (cons (cons x fresh) ρ)
                      (cons (cons fresh rands) σ) κ))))))
    ((ap rator rands ρ σ (cons φ κ))
     (set! tracer-context (add-trace-transition tracer-context (apply-nat-fun rator (length rands))))
     (ko φ (apply rator rands) ρ σ κ))
    ((ko (randk rands vs ρ) v ρ* σ κ)
     ;(set! tracer-context (add-trace-transition tracer-context (put-val ρ σ))) TODO not necessary since it should already be done in an earlier step?
     (ev (car rands) ρ σ (cons (randk (cdr rands) (cons v vs) ρ) κ)))
    ((ko (ifk _ e2 ρ) #f ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (rem-val)))
     (ev e2 ρ σ κ))
    ((ko (ifk e1 _ ρ) _ ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (rem-val)))
     (ev e1 ρ σ κ))
    ((ko (seqk (list e) ρ) _ ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ* σ)))
     (ev e ρ* σ κ))
    ((ko (seqk (cons e exps) ρ) _ ρ* σ κ)
     (set! tracer-context (add-trace-transition tracer-context (set-env-store ρ* σ)))
     (ev e ρ* σ (cons (seqk exps ρ*) κ)))
    ((ko (haltk) v _ _ _)
     #f))
   tracer-context))

(struct traced-state (ρ σ values))

(define (new-traced-state)
  (traced-state '() '() '()))

(define (step-trace s instruction)
  (match instruction
    ((def-var var-name symbol)
     (struct-copy traced-state s (ρ (cons (cons var-name symbol) (traced-state-ρ s)))))
    ((assign-var symbol value)
     (struct-copy traced-state s (σ (cons (cons symbol value) (traced-state-ρ s)))))
    ((set-env ρ*)
     (struct-copy traced-state s (ρ ρ*)))
    ((set-store σ*)
     (struct-copy traced-state s (σ σ*)))
    ((set-env-store ρ* σ*)
     (struct-copy traced-state s (ρ ρ*) (σ σ*)))
    ((apply-nat-fun nat-fun n)
     (print nat-fun)
     (let* ((vals (take (traced-state-values s) n))
            (result (apply nat-fun vals)))
     (struct-copy traced-state s (values (cons result (drop (traced-state-values s) n))))))
    ((put-val val)
     (struct-copy traced-state s (values (cons val (traced-state-values s)))))
    ((put-var-lookup var-name)
     (let ((binding (assoc var-name (traced-state-ρ s)))
           (val '()))
       (if binding
           (let* ((symbol (cdr binding))            
                  (value (cdr (assoc symbol (traced-state-σ s)))))
             (set! val value))
           (set! val (eval var-name (make-base-namespace))))
       (struct-copy traced-state s (values (cons val (traced-state-values s))))))
    ((rem-val)
     (struct-copy traced-state s (values (cdr (traced-state-values s)))))))

(define (run-trace traced-state transitions)
  (if (null? transitions)
      traced-state
      (let ((new-traced-state (step-trace traced-state (car transitions))))
        (run-trace new-traced-state (cdr transitions)))))

(define (launch-trace tracer-context)
  (run-trace (new-traced-state)
             (tracer-context-trace-transitions tracer-context)))

(define (extract s)
  (match s
    ((finished-run (ko (haltk) v _ _ _) tracer-context) (finished-run v tracer-context))
    (_ 'error)))

(define (state-eval e tracer-context)
  (extract (run (inject e) tracer-context)))

; inject expression into eval state
(define (inject e)
  (let ((apply-sym (gensym)))
    (ev e (list (cons 'apply apply-sym)) (list (cons apply-sym clo-apply)) `(,(haltk)))))

(struct finished-run (value tracer-context))

; run
(define (run s tracer-context)
  (match s
    ((ko (haltk) v _ _ _)
     (finished-run s tracer-context)) ; exit
    (s
     (let* ((step-added-tracer-context (add-to-trace tracer-context s))
            (new-state-tracer-context (step s step-added-tracer-context)))
       (run (state-tracer-context-state new-state-tracer-context)
            (state-tracer-context-tracer-context new-state-tracer-context))))))

#|
; run with tracing
(define (trace-run s expression tracer-context τ)
  (match s
    ((ko (haltk) v _ _ _)
     (cons v (stop-tracing tracer-context))) ;exit
    ((ev `(loop ,e) ρ σ κ) ;doesn't check whether the loop is actually closed
     (if (is-tracing-expression? tracer-context e)
         (let ((c (compile-trace (reverse τ))))
           (run s c))
         'TODO)) ; back to regular running
    (s (trace-run (step s) (cons s τ))))) ; continue tracing

|#

; dummy compiler
(define (compile-trace tracer-context)
  (display "COMPILED ") (display (tracer-context-trace tracer-context)) (newline)
  tracer-context)

; dummy trace runner that falls back to regular interpreter
;(define (run-trace c s)
 ; (display "RUN") (newline)
  ;s)

(define (loop value tracer-context)
  (newline)
  (display value) (newline)
  (display ">>>")
  (let* ((finished-run (state-eval (read) tracer-context))
         (new-tracer-context (finished-run-tracer-context finished-run)))
    (set! global-tracer-context new-tracer-context)
    (loop (finished-run-value finished-run) new-tracer-context)))

;(define fib-t '(letrec ((fib (lambda (n) (loop (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))) (fib 10)))

(loop "tracing Slip" (new-tracer-context))