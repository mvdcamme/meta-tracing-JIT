#lang racket

;; Slippy: lambda letrec if set! begin quote

;(define fib '(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 10)))

(define ns (make-base-namespace))
(struct ev (e κ) #:transparent)
(struct ko (φ κ) #:transparent)
(struct condk (pes es))
(struct definevk (x)) ;define variable
(struct haltk ())
(struct ifk (e1 e2))
(struct letk (x es))
(struct let*k (x bds es))
(struct randk (e es i))
(struct ratork (i))
(struct seqk (es))
(struct setk (x))
(struct clo (λ ρ))
(struct lam (x es))

(struct save-val () #:transparent)
(struct restore-val () #:transparent)
(struct restore-vals (i) #:transparent)
(struct save-env () #:transparent)
(struct restore-env () #:transparent)
(struct set-env (ρ) #:transparent)
(struct alloc-var (x) #:transparent)
(struct set-var (a) #:transparent)
(struct lookup-var (x) #:transparent)
(struct create-closure (x es) #:transparent)
(struct literal-value (e) #:transparent)
(struct quote-value (e) #:transparent)
(struct apply-native (i) #:transparent)
(struct put-guard-false (state) #:transparent)
(struct put-guard-true (state) #:transparent)
(struct load-state (ρ σ) #:transparent)

(define ρ #f) ; env
(define σ #f) ; store
(define θ #f) ; non-kont stack
(define v #f) ; value
(define τ #f) ; trace

(struct state (e ρ σ κ))

(define (generate-state e κ)
  (state e ρ σ κ))

;
;tracing
;

(define global-tracer-context #f) ;TODO debugging

(struct tracer-context (is-tracing? expression-to-be-traced expressions-already-traced) #:transparent)

(define (new-tracer-context)
  (tracer-context #f #f '())) ;TODO except for debugging, is-tracing? should always start from #f

(define is-tracing? tracer-context-is-tracing?)

(define (is-tracing-expression? tracer-context expression)
  (eq? (tracer-context-expression-to-be-traced tracer-context) expression))

(define (start-tracing-expression old-tracer-context expression)
  (struct-copy tracer-context old-tracer-context (is-tracing? #t) (expression-to-be-traced expression)))

(define (stop-tracing old-tracer-context)
  (struct-copy tracer-context old-tracer-context
               (expressions-already-traced
                (cons (cons (tracer-context-expression-to-be-traced old-tracer-context) τ)
                      (tracer-context-expressions-already-traced old-tracer-context))) ;TODO assumes that the expression hasn't been traced already
               (is-tracing? #f)
               (expression-to-be-traced #f)))

(define (expression-traced? tracer-context expression)
  (assoc expression (tracer-context-expressions-already-traced tracer-context)))

;
;evaluation
;

(define (step-trace m)
  (match m
    ((put-guard-false state)
     (if v
         (begin (display "Guard failed") (newline))
         (begin (display "Guard passed") (newline))))
    ((put-guard-true state)
     (if v
         (begin (display "Guard passed") (newline))
         (begin (display "Guard failed") (newline))))
    ((save-val)
     (set! θ (cons v θ)))
    ((save-env)
     (set! θ (cons ρ θ)))
    ((set-env ρ*)
     (set! ρ ρ*))
    ((restore-env)
     (set! ρ (car θ))
     (set! θ (cdr θ)))
    ((restore-val)
     (set! v (car θ))
     (set! θ (cdr θ)))
    ((restore-vals i)
     (set! v (take θ i))
     (set! θ (drop θ i)))
    ((alloc-var x)
     (let ((a (gensym)))
       (set! ρ (cons (cons x a) ρ))
       (set! σ (cons (cons a v) σ))))
    ((set-var x)
     (let ((a (cdr (assoc x ρ))))
       (set! σ (cons (cons a v) σ))))
    ((lookup-var x)
     (match (assoc x ρ)
       ((cons _ a) (set! v (cdr (assoc a σ))))
       (_ (set! v (eval x ns)))))
    ((create-closure x es)
     (set! v (clo (lam x es) ρ)))
    ((literal-value e)
     (set! v e))
    ((quote-value e)
     (set! v e))
    ((apply-native i)
     (let ((rands (take θ i)))
       (set! θ (drop θ i))
       (set! v (apply v rands))))
    ((load-state ρ* σ*)
     (set! ρ ρ*)
     (set! σ σ*)
     (set! θ '())
     (set! v #f))))
  ;(display θ) (newline) (display "-------------------------------------------") (newline))

(define (run-trace ms)
  (if (pair? ms)
      (begin
        (step-trace (car ms))
        (run-trace (cdr ms)))
      #f))

(define (append-trace ms)
  (and τ (set! τ (append τ ms))))

(define (execute tracer-context . ms)
  (and (is-tracing? tracer-context)
       (append-trace ms))
  (run-trace ms))

(define (eval-seq tracer-context es κ)
  (match es
    ((list e)
     (ev e κ))
    ((cons e es)
     (execute tracer-context
              (save-env))
     (ev e (cons (seqk es) κ)))))

(define (step state tracer-context)
  (cons
   (match state
     ((ev (? symbol? x) (cons φ κ))
      (execute tracer-context
               (lookup-var x))
      (ko φ κ))
     ((ev `(begin ,es ...) κ)
      (eval-seq tracer-context es κ))
     ((ev `(cond) (cons φ κ))
      (execute tracer-context
               (literal-value '()))
      (ko φ κ))
     ((ev `(cond (else . ,es)) κ)
      (eval-seq tracer-context es κ))
     ((ev `(cond (,pred . ,pes) . ,es) κ)
      (execute tracer-context
               (save-env))
      (ev pred (cons (condk pes es) κ)))
     ((ev `(define ,pattern . ,expressions) κ)
      (if (symbol? pattern)
          (begin (execute tracer-context
                          (save-env))
                 (ev (car expressions) (cons (definevk pattern) κ)))
          (begin (execute tracer-context
                          (alloc-var (car pattern))
                          (create-closure (cdr pattern) expressions)
                          (set-var (car pattern)))
                 (match κ
                   ((cons φ κ) (ko φ κ))))))
     ((ev `(if ,e ,e1 ,e2) κ)
      (execute tracer-context
               (save-env))
      (ev e (cons (ifk e1 e2) κ)))
     ((ev `(lambda ,x ,es ...) (cons φ κ))
      (execute tracer-context
               (create-closure x es))
      (ko φ κ))
     ((ev `(let* () . ,expressions) κ)
      (eval-seq tracer-context expressions κ))
     ((ev `(let* ((,var-name ,value) . ,other-bindings) . ,expressions) κ)
      (execute tracer-context
               (save-env))
      (ev value (cons (let*k var-name other-bindings expressions) κ)))
     ((ev `(letrec ((,x ,e)) ,es ...) κ)
      (execute tracer-context
               (literal-value 'undefined)
               (alloc-var x)
               (save-env))
      (ev e (cons (letk x es) κ)))
     ((ev `(quote ,e) (cons φ κ))
      (execute tracer-context
               (quote-value e))
      (ko φ κ))
     ((ev `(set! ,x ,e) κ)
      (execute tracer-context
               (save-env))
      (ev e (cons (setk x) κ)))
     ((ev `(,rator) κ)
      (execute tracer-context
               (save-env))
      (ev rator (cons (ratork 0) κ)))
     ((ev `(,rator . ,rands) κ)
      (execute tracer-context
               (save-env))
      (let ((rrands (reverse rands)))
        (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
     ((ev e (cons φ κ))
      (execute tracer-context
               (literal-value e))
      (ko φ κ))
     ((ko (condk pes es) κ)
      (execute tracer-context
               (restore-env))
      (if v
          (begin (execute tracer-context
                          (put-guard-true (generate-state `(cond ,@es) κ)))
                 (eval-seq tracer-context pes κ))
          (begin (execute tracer-context
                          (put-guard-false (generate-state `(begin ,@pes) κ)))
                 (ev `(cond ,@es) κ))))
     ((ko (definevk x) (cons φ κ))
      (execute tracer-context
               (restore-env)
               (alloc-var x)
               (set-var x))
      (ko φ κ))
     ((ko (letk x es) κ)
      (execute tracer-context
               (restore-env)
               (set-var x))
      (eval-seq tracer-context es κ))
     ((ko (let*k x bds es) κ)
      (execute tracer-context
               (restore-env)
               (alloc-var x)
               (set-var x))
      (ev `(let* ,bds ,@es) κ))
     ((ko (setk x) (cons φ κ))
      (execute tracer-context
               (restore-env)
               (set-var x))
      (ko φ κ))
     ((ko (randk rator '() i) κ)
      (execute tracer-context
               (restore-env)
               (save-val)
               (save-env))
      (ev rator (cons (ratork i) κ)))
     ((ko (randk rator rands i) κ)
      (execute tracer-context
               (restore-env)
               (save-val)
               (save-env))
      (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
     ((ko (ratork i) κ)
      (execute tracer-context
               (restore-env))
      (match v
        ((clo (lam x es) ρ)
         (execute tracer-context
                  (set-env ρ))
         (let loop ((i i) (x x))
           (match x
             ('()
              (eval-seq tracer-context es κ))
             ((cons x xs)
              (execute tracer-context
                       (restore-val)
                       (alloc-var x))
              (loop (- i 1) xs))
             ((? symbol? x)
              (execute tracer-context
                       (restore-vals i)
                       (alloc-var x))
              (eval-seq tracer-context es κ)))))
        (_
         (execute tracer-context
                  (apply-native i))
         (ko (car κ) (cdr κ)))))
     ((ko (ifk e1 e2) κ)
      (execute tracer-context
               (restore-env))
      (if v
          (begin (execute tracer-context
                  (put-guard-true (generate-state e2 κ))) ;If the guard fails, the predicate was false, so e2 should be evaluated
                 (ev e1 κ))
          (begin (execute tracer-context
                  (put-guard-false (generate-state e1 κ))) ;If the guard fails, the predicate was true, so e1 should be evaluated
                 (ev e2 κ))))
     ((ko (seqk '()) (cons φ κ)) ;TODO No tailcall optimization!
      (execute tracer-context
               (restore-env))
      (ko φ κ))
     ((ko (seqk (cons e exps)) κ)
      (ev e (cons (seqk exps) κ)))
     ((ko (haltk) _)
      #f))
   tracer-context))

(define (inject e)
  (ev e `(,(haltk))))

(define (reset)
  (set! ρ '())
  (set! σ '())
  (set! θ '())
  (set! τ '()))

(define (run s)
  (reset)
  (let loop ((s s)
             (tracer-context (new-tracer-context)))
    (match s
      ((ko (haltk) _)
       (set! global-tracer-context tracer-context)
       v)
      ((ev `(can-start-loop ,e) κ)
       (cond ((expression-traced? tracer-context e)
              (display "TODO Switch to trace-execution!")
              (newline)
              ;TODO switch to run-trace
              (let* ((result (step (ev e κ) tracer-context))
                     (new-state (car result))
                     (new-tracer-context (cdr result)))
                (loop new-state new-tracer-context)))
             ((is-tracing-expression? tracer-context e)
              (set! tracer-context (stop-tracing tracer-context))
              ;TODO switch to run-trace
              (let* ((result (step (ev e κ) tracer-context))
                     (new-state (car result))
                     (new-tracer-context (cdr result)))
                (loop new-state new-tracer-context)))
             ((not (is-tracing? tracer-context))
              (set! tracer-context (start-tracing-expression tracer-context e))
              (append-trace (list (load-state ρ σ)))
              (let* ((result (step (ev e κ) tracer-context))
                     (new-state (car result))
                     (new-tracer-context (cdr result)))
                (loop new-state new-tracer-context)))
             (else
              (let* ((result (step (ev e κ) tracer-context))
                     (new-state (car result))
                     (new-tracer-context (cdr result)))
                (loop new-state new-tracer-context)))))
      (_
       (let* ((result (step s tracer-context))
              (new-state (car result))
              (new-tracer-context (cdr result)))
         (loop new-state new-tracer-context))))))