#lang racket

(define meta-level-apply apply)

(define meta-level-eval eval)

(define ns (make-base-namespace))
(struct ev (e ρ σ κ)) ;state: (expression environment store list-of-continuations)
(struct ko (φ v ρ σ κ)) ;continuation: (current-continuation value store list-of-continuations)
(struct ap (v vs ρ σ κ)) ;application: (operator values environment store continuation)
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

(define list-of-expressions '())

(struct tracer-context (is-tracing? expression-to-be-traced expressions-already-traced trace) #:transparent)

(define (new-tracer-context)
    (tracer-context #f #f '() '()))

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
  (struct-copy tracer-context old-tracer-context (trace (cons expression (tracer-context-trace old-tracer-context)))))

;(define (add-expression-traced old-tracer-context expression) TODO redundant?
 ; (struct-copy tracer-context old-tracer-context (expressions-already-traced (cons expression (vector-ref tracer-context 2)))))

;
;evaluation
;

(struct evaluated-expression (expression tracer-context))

(define (eval-seq es ρ σ κ)
  (match es
    ((list e) (ev e ρ σ κ))
    ((cons e es) (ev e ρ σ (cons (seqk es ρ) κ)))))

(define (step state)
  (match state
    ((ev (and x (? symbol?)) ρ σ (cons φ κ))
     (ko φ (match (assoc x ρ)
             ((cons _ a) (cdr (assoc a σ)))
             (_ (eval x ns))) ρ σ κ)) ;symbol wasn't found in environment -> check in Racket namespace
    ((ev `(begin ,es ...) ρ σ κ)
     (eval-seq es ρ σ κ))
    ((ev `(can-start-loop ,e) ρ σ κ)
     (ev e ρ σ (cons (can-start-loopk ρ) κ)))
    ((ev `(cond ()) ρ σ (cons φ κ))
     (ko φ '() ρ σ κ))
    ((ev `(cond (else . ,expressions)) ρ σ κ)
     (eval-seq expressions ρ σ κ))
    ((ev `(cond (,pred . ,pred-expressions) . ,expressions) ρ σ κ)
     (ev pred ρ σ (cons (condk pred-expressions expressions ρ) κ)))
    ((ev `(define ,pattern . ,expressions) ρ σ (cons φ κ))
     (if (symbol? pattern)
          (let* ((fresh (gensym))
                 (ρ* (cons (cons pattern fresh) ρ)))
            (ev (car expressions) ρ σ (cons (definevk fresh ρ*) (cons φ κ)))) ;TODO find a better solution for match of (cons φ κ)?
          (let* ((fresh (gensym))
                 (ρ* (cons (cons (car pattern) fresh) ρ))
                 (procedure (clo (lam (cdr pattern) expressions) ρ*))
                 (σ* (cons (cons fresh procedure) σ)))
              (ko φ procedure ρ* σ* κ))))
    ((ev `(lambda ,x ,es ...) ρ σ (cons φ κ))
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
       (ev e ρ* σ (cons (letk fresh es ρ*) κ))))
    ((ev `(quote ,e) ρ σ (cons φ κ))
     (ko φ e ρ σ κ))
    ((ev `(set! ,x ,e) ρ σ κ)
     (ev e ρ σ (cons (setk x ρ) κ)))
    ((ev `(,rator . ,rands) ρ σ κ)
     (ev rator ρ σ (cons (randk rands '() ρ) κ)))
    ((ev e ρ σ (cons φ κ)) ;literal
     (ko φ e ρ σ κ))
    ((ko (condk pred-expressions expressions ρ) pred-value ρ* σ κ)
     (if pred-value
         (eval-seq pred-expressions ρ σ κ)
         (ev `(cond ,@expressions) ρ σ κ)))
    ((ko (definevk x ρ*) v ρ σ (cons φ κ))
     (let ((σ* (cons (cons x v) σ)))
       (ko φ v ρ* σ* κ)))
    ((ko (letk a es ρ) v ρ σ κ)
     (let ((σ* (cons (cons a v) σ)))
       (eval-seq es ρ σ* κ)))
    ((ko (let*k var-name other-bindings expressions ρ) value ρ* σ κ)
     (let* ((fresh (gensym))
            (ρ* (cons (cons var-name fresh) ρ))
            (σ* (cons (cons fresh value) σ)))
       (ev `(let* ,other-bindings ,@expressions) ρ* σ* κ)))
    ((ko (setk x ρ) v ρ σ (cons φ κ))
     (match (assoc x ρ)
       ((cons name a) (ko φ v ρ (cons (cons a v) σ) κ))))
    ((ko (randk '() vs ρ) v ρ σ κ)
     (let ((vs (reverse (cons v vs))))
       (ap (car vs) (cdr vs) ρ σ κ)))
    ((ap (clo (lam x es) ρ*) rands ρ σ κ)
     (let loop ((x x) (rands rands) (ρ ρ*) (σ σ))
       (match x
         ('() (eval-seq es ρ σ κ))
         ((cons x xs)
          (let ((fresh (gensym)))
            (loop xs (cdr rands)
                  (cons (cons x fresh) ρ)
                  (cons (cons fresh (car rands)) σ))))
         ((and x (? symbol?))
          (let ((fresh (gensym)))
            (eval-seq es
                      (cons (cons x fresh) ρ)
                      (cons (cons fresh rands) σ) κ))))))
    ((ap rator rands ρ σ (cons φ κ))
     (ko φ (apply rator rands) ρ σ κ))
    ((ko (randk rands vs ρ) v ρ* σ κ)
     (ev (car rands) ρ σ (cons (randk (cdr rands) (cons v vs) ρ) κ)))
    ((ko (ifk _ e2 ρ) #f ρ* σ κ)
     (ev e2 ρ σ κ))
    ((ko (ifk e1 _ ρ) _ ρ* σ κ)
     (ev e1 ρ σ κ))
    ((ko (seqk (list e) ρ) _ ρ* σ κ)
     (ev e ρ* σ κ))
    ((ko (seqk (cons e exps) ρ) _ ρ* σ κ)
     (ev e ρ* σ (cons (seqk exps ρ*) κ)))
    ((ko (haltk) v _ _ _)
     #f)))

(define (extract s)
  (match s
    ((finished-run (ko (haltk) v _ _ _) tracer-context) (finished-run v tracer-context))
    (_ 'error)))

(define (state-eval e tracer-context)
  (extract (run (inject e) tracer-context)))

#|

We can also gather the visited states in a list.

And use it to create a trace of the program.

(define s0 (inject e)) ; initial state
(define τ (trace s0)) ; trace it

|#

(define (trace s)
  (if s
      (append `(,s) (trace (step s)))
      '()))

; inject expression into eval state
(define (inject e)
  (ev e '() '() `(,(haltk))))

(struct finished-run (value tracer-context))

; run
(define (run s tracer-context)
  (match s
    ((ko (haltk) v _ _ _)
     (finished-run s tracer-context)) ; exit
    ((ko (can-start-loopk ρ) v ρ* σ κ) ; intercept "loop" annotation
     (let ((s* (ev v ρ σ κ)))
       (cond ((expression-traced? tracer-context v) ; if compiled trace
              (run (run-trace tracer-context s*) tracer-context)) ; run compiled trace with fallback
             ((is-tracing-expression? tracer-context v)
              (let ((compiled-tracer-context (compile-trace (reverse tracer-context))))
                (run s compiled-tracer-context)))
             (else (run s* (start-tracing-expression tracer-context v)))))) ; run with tracing on
    (s
     (run (step s) (if (is-tracing? tracer-context) ;add the state to the trace if tracing, otherwise just step
                       (add-to-trace tracer-context s)
                       tracer-context)))))

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
(define (run-trace c s)
  (display "RUN") (newline)
  s)

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