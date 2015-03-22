(module cesk-interpreter racket
  
  (provide step)
  
  (require "closures.scm"
           "continuations.scm"
           "instruction-set.scm"
           "interaction.scm"
           "output.scm")
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;                                                                                                      ;
  ;                                         Running evaluator                                            ;
  ;                                                                                                      ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;
  ; Auxiliary functions
  ;
  
  (define (eval-seq program-state es κ)
    (match es
      ('()
       (execute/trace program-state
                      (ko (car κ) (cdr κ))
                      (literal-value '())
                      (pop-continuation)))
      ((list e)
       (execute/trace program-state
                      (ev e κ)
                      '()))
      ((cons e es)
       (execute/trace program-state
                      (save-env)
                      (ev e (cons (seqk es) κ))
                      (push-continuation (seqk es))))))
  
  (define (do-function-call program-state i κ)
    (match (program-state-v program-state)
      ((clo (lam x es) ρ)
       (let loop ((i i) (x x) (instructions (list (prepare-function-call i))))
         (match x
           ('()
            (unless (= i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i))
            (execute/trace program-state
                              (ev `(begin ,@es) (cons (applicationk (lam x es)) κ))
                              (append instructions
                                      (list (push-continuation (applicationk (lam x es)))))))
           ((cons x xs)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
            (let ((new-instructions (list (restore-val)
                                          (alloc-var x))))
              (loop (- i 1) xs (append instructions new-instructions))))
           ((? symbol? x)
            (when (< i 0)
              (error "Incorrect number of args: " (lam x es) "case 3"))
            (execute/trace program-state
                              (ev `(begin ,@es) (cons (applicationk (lam x es)) κ))
                              (append instructions
                                      (list (restore-vals i)
                                            (alloc-var x)
                                            (push-continuation (applicationk (lam x es))))))))))
      (_
       (execute/trace program-state
                         (ko (car κ) (cdr κ))
                         (apply-native i)
                         (pop-continuation)))))
  
  ;
  ; Execute/trace
  ;
  
  (define (execute/trace program-state new-ck-state . ms)
    (define (loop program-state instructions)
      (cond ((null? instructions) (cesk-normal-return (program-state-copy program-state
                                                                          (ck new-ck-state))
                                                      ms))
                        ;; Assumes that no abnormal actions can take place during
                        ;; regular program interpretation.
                        ;; TODO This should be reasonable but check nonetheless
            (else (loop (normal-return-program-state ((car instructions) program-state))
                        (cdr instructions)))))
    (loop program-state ms))
  
  ;
  ; Guard counter
  ;
  
  (define guard-id 0)
  
  (define (inc-guard-id!)
    (let ((temp guard-id))
      (set! guard-id (+ guard-id 1))
      temp))
  
  ;
  ; Step
  ;
  
  (define (step program-state)
    (match program-state
      ((ev `(and ,e . ,es) κ)
       (execute/trace program-state
                      (ev e (cons (andk es) κ))
                      (push-continuation (andk es))))
      ((ev `(apply ,rator ,args) κ)
       (execute/trace program-state
                      (ev args (cons (applyk rator) κ))
                      (push-continuation (applyk rator))))
      ((ev (? symbol? x) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (lookup-var x)
                      (pop-continuation)))
      ((ev `(begin ,es ...) κ)
       (eval-seq program-state es κ))
      ((ev `(can-close-loop ,e) κ)
       (execute/trace program-state
                      (ev e (cons (can-close-loopk) κ))
                      (push-continuation (can-close-loopk))))
      ((ev `(can-start-loop ,e ,debug-info) κ)
       (execute/trace program-state
                      (ev debug-info (cons (can-start-loopk e '()) κ))
                      (push-continuation (can-start-loopk e '()))))
      ((ev `(cond) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (literal-value '())
                      (pop-continuation)))
      ((ev `(cond (else . ,es)) κ)
       (eval-seq program-state es κ))
      ((ev `(cond (,pred . ,pes) . ,es) κ)
       (execute/trace program-state
                      (ev pred (cons (condk pes es) κ))
                      (save-env)
                      (push-continuation (condk pes es))))
      ((ev `(define ,pattern . ,expressions) κ)
       (if (symbol? pattern)
           (begin (execute/trace program-state
                                 (ev (car expressions) (cons (definevk pattern) κ))
                                 (save-env)
                                 (push-continuation (definevk pattern))))
           (begin (execute/trace program-state
                                 (ko (car κ) (cdr κ))
                                 (alloc-var (car pattern))
                                 (create-closure (cdr pattern) expressions)
                                 (set-var (car pattern))
                                 (pop-continuation)))))
      ((ev `(if ,e ,e1 . ,e2) κ)
       (execute/trace program-state
                      (ev e (cons (ifk e1 e2) κ))
                      (save-env)
                      (push-continuation (ifk e1 e2))))
      ((ev `(is-evaluating ,e) κ)
       (execute/trace program-state
                      (ev e (cons (is-evaluatingk) κ))
                      (push-continuation (is-evaluatingk))))
      ((ev `(lambda ,x ,es ...) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (create-closure x es)
                      (pop-continuation)))
      ((ev `(let () . ,expressions)  κ)
       (eval-seq program-state expressions κ))
      ((ev `(let ((,var ,val) . ,bds) . ,es) κ)
       (unless (null? bds)
         (error "Syntax error: let used with more than one binding: " bds))
       (execute/trace program-state
                      (ev val (cons (letk var es) κ))
                      (save-env)
                      (push-continuation (letk var es))))
      ((ev `(let* () . ,expressions) κ)
       (eval-seq program-state expressions κ))
      ((ev `(let* ((,var ,val) . ,bds) . ,es) κ)
       (execute/trace program-state
                      (ev val (cons (let*k var bds es) κ))
                      (save-env)
                      (push-continuation (let*k var bds es))))
      ((ev `(letrec ((,x ,e) . ,bds) . ,es) κ)
       (execute/trace program-state
                      (ev e (cons (letreck x bds es) κ))
                      (literal-value '())
                      (alloc-var x)
                      (save-env)
                      (push-continuation (letreck x bds es))))
      ((ev `(or ,e . ,es) κ)
       (execute/trace program-state
                      (ev e (cons (ork es) κ))
                      (push-continuation (ork es))))
      ((ev `(quote ,e) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (quote-value e)
                      (pop-continuation)))
      ((ev `(set! ,x ,e) κ)
       (execute/trace program-state
                      (ev e (cons (setk x) κ))
                      (save-env)
                      (push-continuation  (setk x))))
      ((ev `(,rator) κ)
       (execute/trace program-state
                      (ev rator (cons (ratork 0 'regular-nulary) κ))
                      (save-env)
                      (push-continuation (ratork 0 'regular-nulary))))
      ((ev `(,rator . ,rands) κ)
       (let ((rrands (reverse rands)))
         (execute/trace program-state
                        (ev (car rrands) (cons (randk rator (cdr rrands) 1) κ))
                        (save-env)
                        (push-continuation (randk rator (cdr rrands) 1)))))
      ((ev e (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (literal-value e)
                      (pop-continuation)))
      ((ko (andk '()) κ)
       (execute/trace program-state
                      (ko (car κ) (cdr κ))
                      (pop-continuation)))
      ((ko (andk '()) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (pop-continuation)))
      ((ko (andk es) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev (car es) (cons (andk (cdr es)) κ))
                                 (push-continuation  (andk (cdr es)))))
           (begin (execute/trace program-state
                                 (ko (car κ) (cdr κ))
                                 (pop-continuation)))))
      ((ko (applicationk debug) κ)
       (execute/trace program-state
                      (restore-env)
                      (ko (car κ) (cdr κ))
                      (pop-continuation)))
      ((ko (apply-failedk rator i) κ)
       (execute/trace program-state
                      (ev rator (cons (ratork i 'apply) κ))
                      (save-all-vals)
                      (save-env)
                      (push-continuation (ratork i 'apply))))
      ((ko (applyk rator) κ)
       (let ((i (length (program-state-v program-state))))
         (execute/trace program-state
                        (ev rator (cons (ratork i 'apply) κ))
                        (guard-same-nr-of-args i rator (inc-guard-id!))
                        (save-all-vals)
                        (save-env)
                        (push-continuation (ratork i 'apply)))))
      ((ko (closure-guard-failedk i) κ)
       (do-function-call program-state i κ)) ;TODO
      ((ko (condk pes '()) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes) κ)
                                 (restore-env)
                                 (guard-true (inc-guard-id!) '())))
           (begin (execute/trace program-state
                                 (ko (car κ) (cdr κ))
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))
                                 (literal-value '())
                                 (pop-continuation)))))
      ((ko (condk pes `((else . ,else-es))) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes) κ)
                                 (restore-env)
                                 (guard-true (inc-guard-id!) `(begin ,@else-es))))
           (begin (execute/trace program-state
                                 (ev `(begin ,@else-es) κ)
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))))))
      ((ko (condk pes `((,pred . ,pred-es) . ,es)) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes) κ)
                                 (restore-env)
                                 (guard-true (inc-guard-id!) `(cond ,@es))))
           (begin (execute/trace program-state
                                 (ev pred (cons (condk pred-es es) κ))
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))
                                 (save-env)
                                 (push-continuation (condk pred-es es))))))
      ((ko (definevk x) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (restore-env)
                      (alloc-var x)
                      (pop-continuation)))
      ((ko (haltk) _)
       #f) ;TODO
      ((ko (ifk e1 e2) κ)
       (execute/trace (restore-env))
       (let ((new-guard-id (inc-guard-id!)))
         (if (program-state-v program-state)
             (begin (execute/trace program-state
                                   (ev e1 κ)
                                   (restore-env)
                                   (guard-true new-guard-id (if (null? e2)
                                                                '()
                                                                ;; If the guard fails, the predicate was false, so e2 should be evaluated
                                                                (car e2)))))
             ;; If the guard fails, the predicate was true, so e1 should be evaluated
             (if (null? e2)
                 (begin (execute/trace program-state
                                       (ko (car κ) (cdr κ))
                                       (restore-env)
                                       (guard-false new-guard-id e1)
                                       (pop-continuation)
                                       (literal-value '())))
                 (execute/trace program-state
                                (ev (car e2) κ)
                                (restore-env)
                                (guard-false new-guard-id e1))))))
      ((ko (letk x es) κ)
       (execute/trace program-state
                      (ev `(begin ,@es) κ)
                      (restore-env)
                      (alloc-var x)))
      ((ko (let*k x '() es) κ)
       (execute/trace program-state
                      (ev `(begin ,@es) κ)
                      (restore-env)
                      (alloc-var x)))
      ((ko (let*k x `((,var ,val) . ,bds) es) κ)
       (execute/trace program-state
                      (ev val (cons (let*k var bds es) κ))
                      (restore-env)
                      (alloc-var x)
                      (save-env)
                      (push-continuation (let*k var bds es))))
      ((ko (letreck x '() es) κ)
       (execute/trace program-state
                      (ev `(begin ,@es) κ)
                      (restore-env)
                      (set-var x)))
      ((ko (letreck x `((,var ,val) . ,bds) es) κ)
       (execute/trace program-state
                      (ev val (cons (letreck var bds es) κ))
                      (restore-env)
                      (set-var x)
                      (alloc-var var)
                      (save-env)
                      (push-continuation (letreck var bds es))))
      ((ko (ork '()) κ)
       (execute/trace program-state
                      (ko (car κ) (cdr κ))
                      (pop-continuation)))
      ((ko (ork es) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ko (car κ) (cdr κ))
                                 (pop-continuation)))
           (execute/trace program-state
                          (ev `(or ,@es) κ)
                          '())))
      ((ko (randk rator '() i) κ)
       (execute/trace program-state
                      (ev rator (cons (ratork i 'regular) κ))
                      (restore-env)
                      (save-val)
                      (save-env)
                      (push-continuation (ratork i 'regular))))
      ((ko (randk rator rands i) κ)
       (execute/trace program-state
                      (ev (car rands) (cons (randk rator (cdr rands) (+ i 1)) κ))
                      (restore-env)
                      (save-val)
                      (save-env)
                      (push-continuation (randk rator (cdr rands) (+ i 1)))))
      ((ko (ratork i debug) κ) ;TODO code duplication: inlined do-function-call!!!
       (match (program-state-v program-state)
         ((clo (lam x es) ρ)
          (let loop ((i i) (x x) (instructions (list (restore-env)
                                                     (guard-same-closure (program-state-v program-state) i (inc-guard-id!))
                                                     (prepare-function-call i))))
            (match x
              ('()
               (unless (= i 0)
                 (error "Incorrect number of args: " (lam x es) ", i = " i))
               (execute/trace program-state
                              (ev `(begin ,@es) (cons (applicationk (lam x es)) κ))
                              (append instructions
                                      (list (push-continuation (applicationk (lam x es)))))))
              ((cons x xs)
               (when (< i 0)
                 (error "Incorrect number of args: " (lam x es) ", i = " i ", args left = " (cons x xs)))
               (let ((new-instructions (list (restore-val)
                                             (alloc-var x))))
                 (loop (- i 1) xs (append instructions new-instructions))))
              ((? symbol? x)
               (when (< i 0)
                 (error "Incorrect number of args: " (lam x es) "case 3"))
               (execute/trace program-state
                              (ev `(begin ,@es) (cons (applicationk (lam x es)) κ))
                              (append instructions
                                      (list (restore-vals i)
                                            (alloc-var x)
                                            (push-continuation (applicationk (lam x es))))))))))
         (_
          (execute/trace program-state
                         (ko (car κ) (cdr κ))
                         (restore-env)
                         (guard-same-closure (program-state-v program-state) i (inc-guard-id!))
                         (apply-native i)
                         (pop-continuation)))))
      ((ko (seqk '()) (cons φ κ)) ; No tailcall optimization!
       (execute/trace program-state
                      (ko φ κ)
                      (restore-env)
                      (pop-continuation)))
      ((ko (seqk (cons e exps)) κ)
       (execute/trace program-state
                      (ev e (cons (seqk exps) κ))
                      (push-continuation (seqk exps))))
      ((ko (setk x) (cons φ κ))
       (execute/trace program-state
                      (ko φ κ)
                      (restore-env)
                      (set-var x)
                      (pop-continuation)))))
    
  
  )
