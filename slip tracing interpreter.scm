#lang racket

;; Slippy: lambda letrec if set! begin quote

;(define fib '(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 10)))

(define ns (make-base-namespace))
(struct ev (e κ) #:transparent)
(struct ko (φ κ) #:transparent)
(struct definevk (x)) ;define variable
(struct letk (x es))
(struct setk (x))
(struct ifk (e1 e2))
(struct seqk (es))
(struct ratork (i))
(struct randk (e es i))
(struct haltk ())
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

(define ρ #f) ; env
(define σ #f) ; store
(define θ #f) ; non-kont stack
(define v #f) ; value
(define τ #f) ; trace

(define (step-trace m)
  (match m
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
       (set! v (apply v rands))))))

(define (run-trace ms)
  (if (pair? ms)
      (begin
        (step-trace (car ms))
        (run-trace (cdr ms)))
      #f))

(define (append-trace ms)
  (and τ (set! τ (append τ ms))))

(define (execute . ms)
  (append-trace ms)
  (run-trace ms))

(define (eval-seq es κ)
  (match es
    ((list e)
     (ev e κ))
    ((cons e es)
     (execute
      (save-env))
     (ev e (cons (seqk es) κ)))))
(define (step state)
  (match state
    ((ev (? symbol? x) (cons φ κ))
     (execute
      (lookup-var x))
      (ko φ κ))
    ((ev `(define ,pattern . ,expressions) κ)
     (if (symbol? pattern)
         (begin (execute
                 (save-env))
                (ev (car expressions) (cons (definevk pattern) κ)))
         (begin (execute
                 (alloc-var (car pattern))
                 (create-closure (cdr pattern) expressions)
                 (set-var (car pattern)))
                (match κ
                  ((cons φ κ) (ko φ κ))))))
    ((ev `(lambda ,x ,es ...) (cons φ κ))
     (execute
      (create-closure x es))
     (ko φ κ))
    ((ev `(quote ,e) (cons φ κ))
     (execute
      (quote-value e))
     (ko φ κ))
    ((ev `(if ,e ,e1 ,e2) κ)
     (execute
      (save-env))
     (ev e (cons (ifk e1 e2) κ)))
    ((ev `(letrec ((,x ,e)) ,es ...) κ)
     (execute
      (literal-value 'undefined)
      (alloc-var x)
      (save-env))
     (ev e (cons (letk x es) κ)))
    ((ev `(set! ,x ,e) κ)
     (execute
      (save-env))
     (ev e (cons (setk x) κ)))
    ((ev `(begin ,es ...) κ)
     (eval-seq es κ))
    ((ev `(,rator) κ)
     (execute
      (save-env))
     (ev rator (cons (ratork 0) κ)))
    ((ev `(,rator . ,rands) κ)
     (execute
      (save-env))
     (let ((rrands (reverse rands)))
       (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))))
    ((ev e (cons φ κ))
     (execute
      (literal-value e))
     (ko φ κ))
    ((ko (definevk x) (cons φ κ))
     (execute
      (restore-env)
      (alloc-var x)
      (set-var x))
     (ko φ κ))
    ((ko (letk x es) κ)
     (execute
      (restore-env)
      (set-var x))
     (eval-seq es κ))
    ((ko (setk x) (cons φ κ))
     (execute
      (restore-env)
      (set-var x))
     (ko φ κ))
    ((ko (randk rator '() i) κ)
     (execute
      (restore-env)
      (save-val)
      (save-env))
     (ev rator (cons (ratork i) κ)))
    ((ko (randk rator rands i) κ)
     (execute
      (restore-env)
      (save-val)
      (save-env))
     (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ)))
    ((ko (ratork i) κ)
     (execute
      (restore-env))
     (match v
       ((clo (lam x es) ρ)
        (execute
         (set-env ρ))
        (let loop ((i i) (x x))
          (match x
            ('()
             (eval-seq es κ))
            ((cons x xs)
             (execute
              (restore-val)
              (alloc-var x))
              (loop (- i 1) xs))
            ((? symbol? x)
             (execute
              (restore-vals i)
              (alloc-var x))
             (eval-seq es κ)))))
       (_
        (execute
         (apply-native i))
        (ko (car κ) (cdr κ)))))
    ((ko (ifk e1 e2) κ)
     (execute
      (restore-env))
     (if v
         (ev e1 κ)
         (ev e2 κ)))
    ((ko (seqk '()) (cons φ κ)) ;TODO No tailcall optimization!
     (execute
      (restore-env))
     (ko φ κ))
    ((ko (seqk (cons e exps)) κ)
     (ev e (cons (seqk exps) κ)))
    ((ko (haltk) _)
     #f)))

(define (inject e)
  (ev e `(,(haltk))))

(define (reset)
  (set! ρ '())
  (set! σ '())
  (set! θ '())
  (set! τ '()))

(define (run s)
  (reset)
  (let loop ((s s))
    (match s
      ((ko (haltk) _)
       v)
      (_ (loop (step s))))))