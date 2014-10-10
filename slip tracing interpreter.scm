#lang racket

;; Slippy: lambda letrec if set! begin quote

(define ns (make-base-namespace))
(struct ev (e κ) #:transparent)
(struct ko (φ κ) #:transparent)
(struct applicationk () #:transparent)
(struct condk (pes es))
(struct definevk (x)) ;define variable
(struct haltk ())
(struct ifk (e1 e2))
(struct letk (x es))
(struct let*k (x bds es))
(struct randk (e es i))
(struct ratork (i))
(struct closure-guard-validatedk (i))
(struct seqk (es))
(struct setk (x))
(struct clo (λ ρ))
(struct lam (x es))

(define (clo-equal? clo1 clo2)
  (and (equal? (lam-x (clo-λ clo1)) (lam-x (clo-λ clo2)))
       (equal? (lam-es (clo-λ clo1)) (lam-es (clo-λ clo2)))
       (equal? (clo-ρ clo1) (clo-ρ clo2))))

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

(define (expression-trace tracer-context expression)
  (cdr (assoc expression (tracer-context-expressions-already-traced tracer-context))))

;
;evaluation
;

(define (put-guard-false tracer-context e)
  (if v
      (begin (display "Guard failed") (newline) (bootstrap e tracer-context))
      (begin (display "Guard passed") (newline))))

(define (put-guard-true tracer-context e)
  (if v
      (begin (display "Guard passed") (newline))
      (begin (display "Guard failed") (newline) (bootstrap e tracer-context))))

(define (put-guard-same-closure tracer-context clo i)
  (and (not (clo-equal? v clo))
       (display "Closure guard failed") (newline)
       (bootstrap-from-continuation (closure-guard-validatedk i) tracer-context)))

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
  (match (assoc x ρ)
    ((cons _ a) (set! v (cdr (assoc a σ))))
    (_ (set! v (eval x ns)))))

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

(define (run-trace tracer-context ms)
  (if (pair? ms)
      (begin
        (eval (car ms))
        (run-trace tracer-context (cdr ms)))
      #f))

(define (append-trace ms)
  (and τ (set! τ (append τ ms))))

(define (execute tracer-context . ms)
  (and (is-tracing? tracer-context)
       (append-trace ms))
  (run-trace tracer-context ms))

(define (eval-seq tracer-context es κ)
  (match es
    ((list e)
     (ev e κ))
    ((cons e es)
     (execute tracer-context
              `(save-env)
              `(add-continuation ,(seqk es)))
     (ev e (cons (seqk es) κ)))))

(define (step state tracer-context)
  (cons
   (match state
     ((ev (? symbol? x) (cons φ κ))
      (execute tracer-context
               `(lookup-var ',x)
               `(remove-continuation))
      (ko φ κ))
     ((ev `(begin ,es ...) κ)
      (eval-seq tracer-context es κ))
     ((ev `(cond) (cons φ κ))
      (execute tracer-context
               `(literal-value ())
               `(remove-continuation))
      (ko φ κ))
     ((ev `(cond (else . ,es)) κ)
      (eval-seq tracer-context es κ))
     ((ev `(cond (,pred . ,pes) . ,es) κ)
      (execute tracer-context
               `(save-env)
               `(add-continuation ,(condk pes es)))
      (ev pred (cons (condk pes es) κ)))
     ((ev `(define ,pattern . ,expressions) κ)
      (if (symbol? pattern)
          (begin (execute tracer-context
                          `(save-env)
                          `(add-continuation ,(definevk pattern)))
                 (ev (car expressions) (cons (definevk pattern) κ)))
          (begin (execute tracer-context
                          `(alloc-var ',(car pattern))
                          `(create-closure ',(cdr pattern) ',expressions)
                          `(set-var ',(car pattern))
                          `(remove-continuation))
                 (match κ
                   ((cons φ κ) (ko φ κ))))))
     ((ev `(if ,e ,e1 ,e2) κ)
      (execute tracer-context
               `(save-env)
               `(add-continuation ,(ifk e1 e2)))
      (ev e (cons (ifk e1 e2) κ)))
     ((ev `(lambda ,x ,es ...) (cons φ κ))
      (execute tracer-context
               `(create-closure ',x ',es)
               `(remove-continuation))
      (ko φ κ))
     ((ev `(let* () . ,expressions) κ)
      (eval-seq tracer-context expressions κ))
     ((ev `(let* ((,var-name ,value) . ,other-bindings) . ,expressions) κ)
      (execute tracer-context
               `(save-env)
               `(add-continuation ,(let*k var-name other-bindings expressions)))
      (ev value (cons (let*k var-name other-bindings expressions) κ)))
     ((ev `(letrec ((,x ,e)) ,es ...) κ)
      (execute tracer-context
               `(literal-value undefined)
               `(alloc-var ',x)
               `(save-env)
               `(add-continuation ,(letk x es)))
      (ev e (cons (letk x es) κ)))
     ((ev `(quote ,e) (cons φ κ))
      (execute tracer-context
               `(quote-value ,e)
               `(remove-continuation))
      (ko φ κ))
     ((ev `(set! ,x ,e) κ)
      (execute tracer-context
               `(save-env)
               `(add-continuation ,(setk x)))
      (ev e (cons (setk x) κ)))
     ((ev `(,rator) κ)
      (execute tracer-context
               `(save-env)
               `(add-continuation ,(ratork 0)))
      (ev rator (cons (ratork 0) κ)))
     ((ev `(,rator . ,rands) κ)
      (execute tracer-context
               `(save-env))
      (let ((rrands (reverse rands)))
        (execute tracer-context
                 `(add-continuation ,(randk rator (cdr rrands) 1)))
        (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
     ((ev e (cons φ κ))
      (execute tracer-context
               `(literal-value ,e)
               `(remove-continuation))
      (ko φ κ))
     ((ko (applicationk) κ)
      (execute tracer-context
               `(restore-env)
               `(remove-continuation))
      (ko (car κ) (cdr κ)))
     ((ko (condk pes es) κ)
      (execute tracer-context
               `(restore-env))
      (if v
          (begin (execute tracer-context
                          `(put-guard-true ,tracer-context ,`(cond ',@es)))
                 (eval-seq tracer-context pes κ))
          (begin (execute tracer-context
                          `(put-guard-false ,tracer-context ,`(begin ',@pes)))
                 (ev `(cond ,@es) κ))))
     ((ko (definevk x) (cons φ κ))
      (execute tracer-context
               `(restore-env)
               `(alloc-var ',x)
               `(set-var ',x)
               `(remove-continuation))
      (ko φ κ))
     ((ko (letk x es) κ)
      (execute tracer-context
               `(restore-env)
               `(set-var ',x))
      (eval-seq tracer-context es κ))
     ((ko (let*k x bds es) κ)
      (execute tracer-context
               `(restore-env)
               `(alloc-var ',x)
               `(set-var ',x))
      (ev `(let* ,bds ,@es) κ))
     ((ko (setk x) (cons φ κ))
      (execute tracer-context
               `(restore-env)
               `(set-var ',x)
               `(remove-continuation))
      (ko φ κ))
     ((ko (randk rator '() i) κ)
      (execute tracer-context
               `(restore-env)
               `(save-val)
               `(save-env)
               `(add-continuation ,(ratork i)))
      (ev rator (cons (ratork i) κ)))
     ((ko (randk rator rands i) κ)
      (execute tracer-context
               `(restore-env)
               `(save-val)
               `(save-env)
               `(add-continuation ,(randk rator (cdr rands) (+ i 1))))
      (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
     ((ko (closure-guard-validatedk i) κ)
      (match v
        ((clo (lam x es) ρ)
         (execute tracer-context
                  `(restore-vals ,i)
                  `(save-env)
                  `(save-vals ,i)
                  `(set-env ',ρ))
         (let loop ((i i) (x x))
           (match x
             ('()
              (execute tracer-context
                       `(add-continuation ,(applicationk)))
              (eval-seq tracer-context es (cons (applicationk) κ)))
             ((cons x xs)
              (execute tracer-context
                       `(restore-val)
                       `(alloc-var ',x))
              (loop (- i 1) xs))
             ((? symbol? x)
              (execute tracer-context
                       `(restore-vals ,i)
                       `(alloc-var ',x)
                       `(add-continuation ,(applicationk)))
              (eval-seq tracer-context es (cons (applicationk) κ))))))))
     ((ko (ratork i) κ)
      (execute tracer-context
               `(restore-env))
      (match v
        ((clo (lam x es) ρ)
         (execute tracer-context
                  `(put-guard-same-closure ,tracer-context ,v ,i)) ;TODO τ-κ does not need to be changed?
         (ko (closure-guard-validatedk i) κ))
        (_
         (execute tracer-context
                  `(apply-native ,i)
                  `(remove-continuation))
         (ko (car κ) (cdr κ)))))
     ((ko (ifk e1 e2) κ)
      (execute tracer-context
               `(restore-env))
      (if v
          (begin (execute tracer-context
                          `(put-guard-true ,tracer-context ',e2)) ;If the guard fails, the predicate was false, so e2 should be evaluated
                 (ev e1 κ))
          (begin (execute tracer-context
                          `(put-guard-false ,tracer-context ',e1)) ;If the guard fails, the predicate was true, so e1 should be evaluated
                 (ev e2 κ))))
     ((ko (seqk '()) (cons φ κ)) ;TODO No tailcall optimization!
      (execute tracer-context
               `(restore-env)
               `(remove-continuation))
      (ko φ κ))
     ((ko (seqk (cons e exps)) κ)
      (execute tracer-context
               `(add-continuation ,(seqk exps)))
      (ev e (cons (seqk exps) κ)))
     ((ko (haltk) _)
      #f))
   tracer-context))

(define (inject e)
  (ev e `(,(haltk))))

(define (reset!)
  (set! ρ '())
  (set! σ '())
  (set! θ '())
  (set! τ '())
  (set! τ-κ `(,(haltk))))

(define (clear-trace!)
  (set! τ '()))

(define (bootstrap e tracer-context)
  (global-continuation (list (ev e τ-κ) tracer-context))) ;step* called with the correct arguments

(define (bootstrap-from-continuation φ tracer-context)
  (global-continuation (list (ko φ τ-κ) tracer-context)))

(define (step* s tracer-context)
  (match s
    ((ko (haltk) _)
     (set! global-tracer-context tracer-context)
     v)
    ((ev `(can-start-loop ,e  . ,debug-info) κ)
     (and (not (null? debug-info))
          (display "tracing loop ") (display (car debug-info)) (newline))
     (cond ((expression-traced? tracer-context e)
            (display "----------- EXECUTING TRACE -----------") (newline)
            (let ((trace (expression-trace tracer-context e)))
              (let loop ()
                (run-trace tracer-context trace)
                (loop))))
           ;(let* ((result (step (ev e κ) tracer-context)) TODO shouldn't be used, except for debugging
           ;      (new-state (car result))
           ;     (new-tracer-context (cdr result)))
           ;(step* new-state new-tracer-context)))
           ((is-tracing-expression? tracer-context e)
            (display "-----------TRACING FINISHED; EXECUTING TRACE -----------") (newline)
            (set! tracer-context (stop-tracing tracer-context))
            (let ((trace (expression-trace tracer-context e)))
              (let loop ()
                (run-trace tracer-context trace)
                (loop))))
           ;(let* ((result (step (ev e κ) tracer-context)) TODO shouldn't be used, except for debugging
           ;      (new-state (car result))
           ;     (new-tracer-context (cdr result)))
           ;(step* new-state new-tracer-context)))
           ((not (is-tracing? tracer-context))
            (display "----------- STARTED TRACING -----------") (newline)
            (clear-trace!)
            (set! tracer-context (start-tracing-expression tracer-context e))
            (let* ((result (step (ev e κ) tracer-context))
                   (new-state (car result))
                   (new-tracer-context (cdr result)))
              (step* new-state new-tracer-context)))
           (else
            (display "----------- ALREADY TRACING ANOTHER EXPRESSION -----------") (newline)
            (let* ((result (step (ev e κ) tracer-context))
                   (new-state (car result))
                   (new-tracer-context (cdr result)))
              (step* new-state new-tracer-context)))))
    (_
     (let* ((result (step s tracer-context))
            (new-state (car result))
            (new-tracer-context (cdr result)))
       (step* new-state new-tracer-context)))))

(define (run s)
  (reset!)
  (apply step* (call/cc (lambda (k) (set! global-continuation k) (list s (new-tracer-context))))))
;(step* s new-tracer-context))

;
;test-cases
;

#|
(run (inject '(begin (define (f x) (+ x 10))
                       (define (g y) (* y 10))
                       (define (loop h i k) (can-start-loop (begin (display (h k)) (newline)
                                                                   (if (< i 0)
                                                                       99
                                                                       (loop g (- i 1) k)))))
                       (loop f 10 9))))

(run (inject '(begin (define (fac x)
                       (can-start-loop (if (< x 2)
                                           1
                                           (* x (fac (- x 1))))
                                       "fac"))
                     (fac 5))))

|#

;(define fib '(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 10)))