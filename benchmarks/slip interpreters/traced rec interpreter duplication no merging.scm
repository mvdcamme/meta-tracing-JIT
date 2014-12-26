
;;; Traced recursive Slip interpreter with annotations for measuring trace duplication but WITHOUT annotations for merging traces.
;;; This interpreter should be executed by the tracing interpreter.
;;; 

(begin
  
  (define (assocv el lst)
    (cond ((null? lst) #f)
          ((eq? (vector-ref (car lst) 0) el) (car lst))
          (else (assocv el (cdr lst)))))
  
  (define debug '())
  
  (define (map f lst)
    (define (loop list acc)
      (if (null? list)
          (reverse acc)
          (loop (cdr list) (cons (begin debug (f (car list))) acc))))
    (loop lst '()))
  
  (define (2-map f list-1 list-2)
    (define (loop list-1 list-2 acc)
      (if (and (null? list-1) (null? list-2))
          (reverse acc)
          (loop (cdr list-1) (cdr list-2) (cons (f (car list-1) (car list-2)) acc))))
    (loop list-1 list-2 '()))
  
  (define (for-each f lst)
    (define (loop list)
      (if (not (null? list))
          (begin (f (car list))
                 (loop (cdr list)))))
    (loop lst)
    (void))
  
  (define meta-circularity-level 0)
  
  ;; Forward referencing
  (define transform-input '())
  
  (define (transform-exp exp)
    (vector exp 0))
  
  (define (unwrap-transformed-exp transformed-ex)
    (vector-ref transformed-ex 0))
  
  (define regular-special-forms '(and
                                  apply
                                  begin
                                  cond
                                  eval
                                  if
                                  load
                                  or))
  
  (define (regular-special-form? operator)
    (member operator regular-special-forms))
  
  (define (transform-regular-special-form input)
    (let* ((operator (car input))
           (operands (cdr input)))
      (transform-exp (cons (transform-exp operator) (map transform-input operands)))))
  
  (define (let-form? operator)
    (or (eq? operator 'let)
        (eq? operator 'let*)
        (eq? operator 'letrec)))
  
  (define (transform-let-form input)
    (let* ((operator (car input))
           (operands (cdr input)))
      (transform-exp (cons (transform-exp operator)
                           (let* ((bindings (car operands))
                                  (var-names (map car bindings))
                                  (values (map cadr bindings)))
                             (cons (2-map (lambda (var value)
                                            (list var (transform-input value)))
                                          var-names
                                          values)
                                   (map transform-input (cdr operands))))))))
  
  (define (quote-form? operator)
    (or (eq? operator 'quote)
        (eq? operator 'quasiquote)
        (eq? operator 'unquote)))
  
  (define (transform-quote-form input)
    (let* ((operator (car input))
           (operands (cdr input)))
      (transform-exp (list (transform-exp operator) (car operands)))))
  
  (define (transform-input-act input)
    (define (tree-rec input)
      (cond ((pair? input)
             (let* ((operator (car input))
                    (operands (cdr input)))
               (cond ((let-form? operator) (transform-let-form input))
                     ((quote-form? operator) (transform-quote-form input))
                     ((regular-special-form? operator) (transform-regular-special-form input))
                     ((eq? operator 'define) (transform-exp (cons (transform-exp 'define) (cons (car operands) (map tree-rec (cdr operands))))))
                     ((eq? operator 'lambda) (transform-exp (cons (transform-exp 'lambda) (cons (car operands) (map tree-rec (cdr operands))))))
                     ((eq? operator 'set!) (transform-exp (cons (transform-exp 'set!) (cons (car operands) (map tree-rec (cdr operands))))))
                     (else (transform-exp (map tree-rec input))))))
            (else (transform-exp input))))
    (tree-rec input))
  
  (set! transform-input transform-input-act)
  
  ;; Binds the symbol 'random to the pseudo-random function that was placed by the
  ;; tracing interpreter in the environment in which this recursive Slip evaluator is running.
  (define random-binding (vector 'random random))
  
  (define environment (list random-binding))
  
  (define (loop output)
    
    (define rollback environment)
    
    (define evaluate '())
    
    (define (abort message qualifier)
      (display message)
      message)
    
    (define (bind-variable variable value)
      (define binding (vector variable value))
      (set! environment (cons binding environment)))
    
    (define (bind-parameters parameters arguments)
      (if (symbol? parameters)
          (bind-variable parameters arguments)
          (if (and (pair? parameters) (pair? arguments))
              (let* ((variable (car parameters))
                     (value (car arguments)))
                (bind-variable variable value)
                (bind-parameters (cdr parameters) (cdr arguments)))
              (if (not (and (null? parameters) (null? arguments)))
                  (error "Incorrect number of arguments, parameters: " parameters ", arguments: " arguments)))))
    
    (define (thunkify expression)
      (define frozen-environment environment)
      (define value (evaluate expression))
      (set! environment frozen-environment)
      value)
    
    (define (evaluate-sequence expressions)
      (if (null? expressions)
          '()
          (let* ((head (car expressions))
                 (tail (cdr expressions))
                 (value (evaluate head)))
            (if (null? tail)
                value
                (evaluate-sequence tail)))))
    
    (define (close parameters expressions)
      (define lexical-environment environment)
      (define (closure . arguments)
        (define dynamic-environment environment)
        (can-start-loop expressions "some function")
        (set! environment lexical-environment)
        (bind-parameters parameters arguments)
        (let* ((value (evaluate-sequence expressions)))
          (set! environment dynamic-environment)
          (can-close-loop expressions "some function")
          value))
      closure)
    
    (define (evaluate-and . expressions)
      (define (and-loop expressions prev)
        (if (null? expressions)
            prev
            (let* ((value (evaluate (car expressions))))
              (if value
                  (and-loop (cdr expressions) value)
                  #f))))
      (and-loop expressions #t))
    
    (define (evaluate-application operator)
      (lambda operands
        (apply (evaluate operator) (map evaluate operands))))
    
    (define (evaluate-apply . expressions)
      (apply (evaluate (car expressions)) (evaluate (cadr expressions))))
    
    (define (evaluate-begin . expressions)
      (evaluate-sequence expressions))
    
    (define (evaluate-cond . expressions)
      (define (cond-loop expressions)
        (cond ((null? expressions) '())
              ((eq? (unwrap-transformed-exp (car (unwrap-transformed-exp (car expressions)))) 'else)
               (if (not (null? (cdr expressions)))
                   (error "Syntax error: 'else' should be at the end of a cond-expression")
                   (evaluate-sequence (cdr (unwrap-transformed-exp (car expressions))))))
              ((not (eq? (evaluate (car (unwrap-transformed-exp (car expressions)))) #f))
               (evaluate-sequence (cdr (unwrap-transformed-exp (car expressions)))))
              (else (cond-loop (cdr expressions)))))
      (cond-loop expressions))
    
    (define (evaluate-define pattern . expressions)
      (if (symbol? pattern)
          (let* ((value (evaluate (car expressions)))
                 (binding (vector pattern value)))
            (set! environment (cons binding environment))
            value)
          (let* ((binding (vector (car pattern) '())))
            (set! environment (cons binding environment))
            (let* ((closure (close (cdr pattern) expressions)))
              (vector-set! binding 1 closure)
              closure))))
    
    (define (evaluate-eval expression)
      (evaluate (evaluate expression)))
    
    (define (evaluate-if predicate consequent . alternate)
      (let* ((cond (evaluate predicate)))
        (if cond
            (thunkify consequent)
            (if (null? alternate)
                '()
                (thunkify (car alternate))))))
    
    (define (evaluate-lambda parameters . expressions)
      (close parameters expressions))
    
    (define (evaluate-let . expressions)
      (define frozen-environment environment)
      (define (evaluate-bindings bindings bindings-to-add)
        (if (null? bindings)
            bindings-to-add
            (let* ((let-binding (car bindings))
                   (variable (car let-binding))
                   (value (evaluate (cadr let-binding)))
                   (binding (vector variable value)))
              (evaluate-bindings (cdr bindings) (cons binding bindings-to-add)))))
      (for-each (lambda (binding) (set! environment (cons binding environment)))
                (evaluate-bindings (car expressions) '()))
      (let* ((value (evaluate-sequence (cdr expressions))))
        (set! environment frozen-environment)
        value))
    
    (define (evaluate-let* bindings . expressions)
      (define frozen-environment environment)
      (define (evaluate-bindings bindings)
        (if (not (null? bindings))
            (let* ((let*-binding (car bindings))
                   (variable (car let*-binding))
                   (value (evaluate (cadr let*-binding)))
                   (binding (vector variable value)))
              (set! environment (cons binding environment))
              (evaluate-bindings (cdr bindings)))))
      (evaluate-bindings bindings)
      (let* ((value (evaluate-sequence expressions)))
        (set! environment frozen-environment)
        value))
    
    (define (evaluate-letrec . expressions)
      (define frozen-environment environment)
      (define (evaluate-bindings bindings)
        (if (not (null? bindings))
            (let* ((letrec-binding (car bindings))
                   (variable (car letrec-binding))
                   (binding (vector variable '())))
              (set! environment (cons binding environment))
              (vector-set! binding 1 (evaluate (cadr letrec-binding)))
              (evaluate-bindings (cdr bindings)))))
      (evaluate-bindings (car expressions))
      (let* ((value (evaluate-sequence (cdr expressions))))
        (set! environment frozen-environment)
        value))
    
    (define (evaluate-load string)
      (let* ((port (open-input-file string))
             (exp (read port))
             (transformed-exp (transform-input exp)))
        (close-input-port port)
        (evaluate transformed-exp)))
    
    (define (evaluate-or . expressions)
      (define (or-loop expressions)
        (if (null? expressions)
            #f
            (let* ((value (evaluate (car expressions))))
              (if value
                  value
                  (or-loop (cdr expressions))))))
      (or-loop expressions))
    
    (define (evaluate-quote expression)
      expression)
    
    (define (evaluate-set! variable expression)
      (define value (evaluate expression))
      (define binding (assocv variable environment))
      (if (vector? binding)
          (vector-set! binding 1 value)
          (abort "inaccessible variable: " variable)))
    
    (define (evaluate-variable variable)
      (define binding (assocv variable environment))
      (if (vector? binding)
          (vector-ref binding 1)
          ((begin debug eval) variable (make-base-namespace))))
    
    (define (actual-evaluate transformed-expression)
      (is-evaluating transformed-expression)
      (let ((expression (unwrap-transformed-exp transformed-expression)))
        (cond
          ((symbol? expression)
           (evaluate-variable expression))
          ((pair? expression)
           (let* ((transformed-operator (car expression))
                  (operator (unwrap-transformed-exp transformed-operator))
                  (operands (cdr expression)))
             (apply
              (cond ((eq? operator 'and)
                     evaluate-and)
                    ((eq? operator 'apply)
                     evaluate-apply)
                    ((eq? operator 'begin)
                     evaluate-begin)
                    ((eq? operator 'cond)
                     evaluate-cond)
                    ((eq? operator 'define) 
                     evaluate-define)
                    ((eq? operator 'eval)
                     evaluate-eval)
                    ((eq? operator 'if) 
                     evaluate-if)
                    ((eq? operator 'lambda) 
                     evaluate-lambda)
                    ((eq? operator 'let)
                     evaluate-let)
                    ((eq? operator 'let*)
                     evaluate-let*)
                    ((eq? operator 'letrec)
                     evaluate-letrec)
                    ((eq? operator 'load) 
                     evaluate-load)
                    ((eq? operator 'or)
                     evaluate-or)
                    ((eq? operator 'quote) 
                     evaluate-quote)
                    ((eq? operator 'set!) 
                     evaluate-set!)
                    (else
                     (evaluate-application transformed-operator))) operands)))
          (else
           expression))))
    
    (set! evaluate actual-evaluate)
    
    (evaluate-load "input_file.scm"))
  
  (loop "Slip"))