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
  ; Special returns
  ;
  
  (define (return-annotation program-state new-c annotation-signal)
    (cesk-normal-return (program-state-copy program-state
                                            (c new-c))
                        '()
                        annotation-signal))
  
  ;
  ; Auxiliary functions
  ;
  
  (define (eval-seq program-state es κ)
    (match es
      ('()
       (execute/trace program-state
                      (ko (car κ))
                      (literal-value '())
                      (pop-continuation)))
      ((list e)
       (execute/trace program-state
                      (ev e)))
      ((cons e es)
       (execute/trace program-state
                      (ev e)
                      (save-env)
                      (push-continuation (seqk es))))))
  
  (define (do-function-call program-state i κ)
    (match (program-state-v program-state)
      ((clo (lam x es) ρ)
       (let loop ((i i) (x x) (instructions (list (prepare-function-call i))))
         (match x
           ('()
            (unless (= i 0)
              (error "Incorrect number of args: " (lam x es) ", i = " i))
            (apply execute/trace
                   (append (list program-state
                                 (ev `(begin ,@es)))
                           instructions
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
            (apply execute/trace
                   (append (list program-state
                                 (ev `(begin ,@es)))
                           instructions
                           (list (restore-vals i)
                                 (alloc-var x)
                                 (push-continuation (applicationk (lam x es))))))))))
      (_
       (execute/trace program-state
                         (ko (car κ))
                         (apply-native i)
                         (pop-continuation)))))
  
  ;
  ; Execute/trace
  ;
  
  (define (execute/trace-aux program-state new-c annotation-signal ms)
    ;; Similar to the (e.g., Haskell) state monad with the program-state as its state.
    (define (>>= program-state instructions)
      (cond ((null? instructions) (cesk-normal-return (program-state-copy program-state
                                                                          (c new-c))
                                                      ms
                                                      annotation-signal))
                        ;; Assumes that no abnormal actions can take place during
                        ;; regular program interpretation.
                        ;; TODO This should be reasonable but check nonetheless
            (else (>>= (normal-return-program-state ((car instructions) program-state))
                       (cdr instructions)))))
    (>>= program-state ms))
  
  (define (execute/trace program-state new-ck-state . ms)
    (execute/trace-aux program-state new-ck-state #f ms))
  
  (define (execute/trace-with-annotation program-state new-ck-state annotation-signal . ms)
    (execute/trace-aux program-state new-ck-state annotation-signal ms))
  
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
  
  (define (make-ck program-state)
    (ck (program-state-c program-state)
        (program-state-κ program-state)))
  
  (define (step program-state)
    (match (make-ck program-state)
      ((ck (ev `(and ,e . ,es)) κ)
       (execute/trace program-state
                      (ev e)
                      (push-continuation (andk es))))
      ((ck (ev `(apply ,rator ,args)) κ)
       (execute/trace program-state
                      (ev args)
                      (push-continuation (applyk rator))))
      ((ck (ev (? symbol? x)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (lookup-var x)
                      (pop-continuation)))
      ((ck (ev `(begin ,es ...)) κ)
       (eval-seq program-state es κ))
      ((ck (ev `(can-close-loop ,e)) κ)
       (execute/trace program-state
                      (ev e)
                      (push-continuation (can-close-loopk))))
      ((ck (ev `(can-start-loop ,e ,debug-info)) κ)
       (execute/trace program-state
                      (ev debug-info)
                      (push-continuation (can-start-loopk e '()))))
      ((ck (ev `(cond)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (literal-value '())
                      (pop-continuation)))
      ((ck (ev `(cond (else . ,es))) κ)
       (eval-seq program-state es κ))
      ((ck (ev `(cond (,pred . ,pes) . ,es)) κ)
       (execute/trace program-state
                      (ev pred)
                      (save-env)
                      (push-continuation (condk pes es))))
      ((ck (ev `(define ,pattern . ,expressions)) κ)
       (if (symbol? pattern)
           (begin (execute/trace program-state
                                 (ev (car expressions))
                                 (save-env)
                                 (push-continuation (definevk pattern))))
           (begin (execute/trace program-state
                                 (ko (car κ))
                                 (alloc-var (car pattern))
                                 (create-closure (cdr pattern) expressions)
                                 (set-var (car pattern))
                                 (pop-continuation)))))
      ((ck (ev `(if ,e ,e1 . ,e2)) κ)
       (execute/trace program-state
                      (ev e)
                      (save-env)
                      (push-continuation (ifk e1 e2))))
      ((ck (ev `(is-evaluating ,e)) κ)
       (execute/trace program-state
                      (ev e)
                      (push-continuation (is-evaluatingk))))
      ((ck (ev `(lambda ,x ,es ...)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (create-closure x es)
                      (pop-continuation)))
      ((ck (ev `(let () . ,expressions))  κ)
       (eval-seq program-state expressions κ))
      ((ck (ev `(let ((,var ,val) . ,bds) . ,es)) κ)
       (unless (null? bds)
         (error "Syntax error: let used with more than one binding: " bds))
       (execute/trace program-state
                      (ev val)
                      (save-env)
                      (push-continuation (letk var es))))
      ((ck (ev `(let* () . ,expressions)) κ)
       (eval-seq program-state expressions κ))
      ((ck (ev `(let* ((,var ,val) . ,bds) . ,es)) κ)
       (execute/trace program-state
                      (ev val)
                      (save-env)
                      (push-continuation (let*k var bds es))))
      ((ck (ev `(letrec ((,x ,e) . ,bds) . ,es)) κ)
       (execute/trace program-state
                      (ev e)
                      (literal-value '())
                      (alloc-var x)
                      (save-env)
                      (push-continuation (letreck x bds es))))
      ((ck (ev `(or ,e . ,es)) κ)
       (execute/trace program-state
                      (ev e)
                      (push-continuation (ork es))))
      ((ck (ev `(quote ,e)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (quote-value e)
                      (pop-continuation)))
      ((ck (ev `(set! ,x ,e)) κ)
       (execute/trace program-state
                      (ev e)
                      (save-env)
                      (push-continuation  (setk x))))
      ((ck (ev `(,rator)) κ)
       (execute/trace program-state
                      (ev rator)
                      (save-env)
                      (push-continuation (ratork 0 'regular-nulary))))
      ((ck (ev `(,rator . ,rands)) κ)
       (let ((rrands (reverse rands)))
         (execute/trace program-state
                        (ev (car rrands))
                        (save-env)
                        (push-continuation (randk rator (cdr rrands) 1)))))
      ((ck (ev e) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (literal-value e)
                      (pop-continuation)))
      ((ck (ko (andk '())) κ)
       (execute/trace program-state
                      (ko (car κ))
                      (pop-continuation)))
      ((ck (ko (andk '())) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (pop-continuation)))
      ((ck (ko (andk es)) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev (car es))
                                 (push-continuation  (andk (cdr es)))))
           (begin (execute/trace program-state
                                 (ko (car κ))
                                 (pop-continuation)))))
      ((ck (ko (applicationk debug)) κ)
       (execute/trace program-state
                      (ko (car κ))
                      (restore-env)
                      (pop-continuation)))
      ((ck (ko (apply-failedk rator i)) κ)
       (execute/trace program-state
                      (ev rator)
                      (save-all-vals)
                      (save-env)
                      (push-continuation (ratork i 'apply))))
      ((ck (ko (applyk rator)) κ)
       (let ((i (length (program-state-v program-state))))
         (execute/trace program-state
                        (ev rator)
                        (guard-same-nr-of-args i rator (inc-guard-id!))
                        (save-all-vals)
                        (save-env)
                        (push-continuation (ratork i 'apply)))))
      ((ck (ko (can-close-loopk)) (cons φ κ))
       (execute/trace-with-annotation program-state
                                      (ko φ)
                                      (can-close-loop-encountered (program-state-v program-state))
                                      (pop-continuation)))
      ((ck (ko (can-start-loopk label '())) κ)
       (execute/trace program-state
                      (ev label)
                      (push-continuation (can-start-loopk '() (program-state-v program-state)))))
      ((ck (ko (can-start-loopk '() debug-info)) (cons φ κ))
       (execute/trace-with-annotation program-state
                                      (ko φ)
                                      (can-start-loop-encountered (program-state-v program-state)
                                                                  debug-info)
                                      (pop-continuation)))
      ((ck (ko (closure-guard-failedk i)) κ)
       (do-function-call program-state i κ))
      ((ck (ko (condk pes '())) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes))
                                 (restore-env)
                                 (guard-true (inc-guard-id!) '())))
           (begin (execute/trace program-state
                                 (ko (car κ))
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))
                                 (literal-value '())
                                 (pop-continuation)))))
      ((ck (ko (condk pes `((else . ,else-es)))) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes))
                                 (restore-env)
                                 (guard-true (inc-guard-id!) `(begin ,@else-es))))
           (begin (execute/trace program-state
                                 (ev `(begin ,@else-es))
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))))))
      ((ck (ko (condk pes `((,pred . ,pred-es) . ,es))) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ev `(begin ,@pes))
                                 (restore-env)
                                 (guard-true (inc-guard-id!) `(cond ,@es))))
           (begin (execute/trace program-state
                                 (ev pred)
                                 (restore-env)
                                 (guard-false (inc-guard-id!) `(begin ,@pes))
                                 (save-env)
                                 (push-continuation (condk pred-es es))))))
      ((ck (ko (definevk x)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (restore-env)
                      (alloc-var x)
                      (pop-continuation)))
      ((ck (ko (haltk)) _)
       (cesk-abnormal-return (cesk-stopped)))
      ((ck (ko (ifk e1 e2)) κ)
       (let ((new-guard-id (inc-guard-id!)))
         (if (program-state-v program-state)
             (begin (execute/trace program-state
                                   (ev e1)
                                   (restore-env)
                                   (guard-true new-guard-id (if (null? e2)
                                                                '()
                                                                ;; If the guard fails, the predicate was false, so e2 should be evaluated
                                                                (car e2)))))
             ;; If the guard fails, the predicate was true, so e1 should be evaluated
             (if (null? e2)
                 (begin (execute/trace program-state
                                       (ko (car κ))
                                       (restore-env)
                                       (guard-false new-guard-id e1)
                                       (pop-continuation)
                                       (literal-value '())))
                 (execute/trace program-state
                                (ev (car e2))
                                (restore-env)
                                (guard-ffalse new-guard-id e1))))))
      ;; Evaluate annotations in step* instead of step
      ;; Annotations might not lead to recursive call to step*
      ((ck (ko (is-evaluatingk)) (cons φ κ))
       (execute/trace-with-annotation program-state
                                      (ko φ)
                                      (is-evaluating-encountered (program-state-v program-state))
                                      (pop-continuation)))
      ((ck (ko (letk x es)) κ)
       (execute/trace program-state
                      (ev `(begin ,@es))
                      (restore-env)
                      (alloc-var x)))
      ((ck (ko (let*k x '() es)) κ)
       (execute/trace program-state
                      (ev `(begin ,@es))
                      (restore-env)
                      (alloc-var x)))
      ((ck (ko (let*k x `((,var ,val) . ,bds) es)) κ)
       (execute/trace program-state
                      (ev val)
                      (restore-env)
                      (alloc-var x)
                      (save-env)
                      (push-continuation (let*k var bds es))))
      ((ck (ko (letreck x '() es)) κ)
       (execute/trace program-state
                      (ev `(begin ,@es))
                      (restore-env)
                      (set-var x)))
      ((ck (ko (letreck x `((,var ,val) . ,bds) es)) κ)
       (execute/trace program-state
                      (ev val)
                      (restore-env)
                      (set-var x)
                      (alloc-var var)
                      (save-env)
                      (push-continuation (letreck var bds es))))
      ((ck (ko (ork '())) κ)
       (execute/trace program-state
                      (ko (car κ))
                      (pop-continuation)))
      ((ck (ko (ork es)) κ)
       (if (program-state-v program-state)
           (begin (execute/trace program-state
                                 (ko (car κ))
                                 (pop-continuation)))
           (execute/trace program-state
                          (ev `(or ,@es)))))
      ((ck (ko (randk rator '() i)) κ)
       (execute/trace program-state
                      (ev rator)
                      (restore-env)
                      (save-val)
                      (save-env)
                      (push-continuation (ratork i 'regular))))
      ((ck (ko (randk rator rands i)) κ)
       (execute/trace program-state
                      (ev (car rands))
                      (restore-env)
                      (save-val)
                      (save-env)
                      (push-continuation (randk rator (cdr rands) (+ i 1)))))
      ((ck (ko (ratork i debug)) κ) ;TODO code duplication: inlined do-function-call!!!
       (match (program-state-v program-state)
         ((clo (lam x es) ρ)
          (let loop ((i i) (x x) (instructions (list (restore-env)
                                                     (guard-same-closure (program-state-v program-state) i (inc-guard-id!))
                                                     (prepare-function-call i))))
            (match x
              ('()
               (unless (= i 0)
                 (error "Incorrect number of args: " (lam x es) ", i = " i))
               (apply execute/trace
                      (append (list program-state
                                    (ev `(begin ,@es)))
                              instructions
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
               (apply execute/trace
                      (append (list program-state
                                    (ev `(begin ,@es)))
                              instructions
                              (list (restore-vals i)
                                    (alloc-var x)
                                    (push-continuation (applicationk (lam x es))))))))))
         (_
          (execute/trace program-state
                         (ko (car κ))
                         (restore-env)
                         (guard-same-closure (program-state-v program-state) i (inc-guard-id!))
                         (apply-native i)
                         (pop-continuation)))))
      ((ck (ko (seqk '())) (cons φ κ)) ; No tailcall optimization!
       (execute/trace program-state
                      (ko φ)
                      (restore-env)
                      (pop-continuation)))
      ((ck (ko (seqk (cons e exps))) κ)
       (execute/trace program-state
                      (ev e)
                      (push-continuation (seqk exps))))
      ((ck (ko (setk x)) (cons φ κ))
       (execute/trace program-state
                      (ko φ)
                      (restore-env)
                      (set-var x)
                      (pop-continuation)))))
  
  )
