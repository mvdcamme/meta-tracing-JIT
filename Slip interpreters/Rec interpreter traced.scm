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
  
  (define (for-each f lst)
    (define (loop list)
      (if (not (null? list))
          (begin (f (car list))
                 (loop (cdr list)))))
    (loop lst)
    (void))
  
  (define meta-circularity-level 0)
  
  ;;; Binds the symbol 'random to the pseudo-random function that was placed by the
  ;;; tracing interpreter in the environment in which this recursive SLIP evaluator is running.
  (define random-binding (vector 'random random))
  
  (define environment (list random-binding))
  
  (define (loop output)
    
    (define rollback environment)
    
    (define evaluate '())
    
    (define (abort message qualifier)
      (display message)
      (loop qualifier))
    
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
    
    (define (return-from-control-flow-split value)
      (merges-control-flow)
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
    
    (define (close parameters expressions closure-name)
      (define lexical-environment environment)
      (define (closure . arguments)
        (define dynamic-environment environment)
        (can-start-loop expressions closure-name)
        (set! environment lexical-environment)
        (bind-parameters parameters arguments)
        (let* ((value (evaluate-sequence expressions)))
          (set! environment dynamic-environment)
          (can-close-loop expressions)
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
              ((eq? (car (car expressions)) 'else)
               (if (not (null? (cdr expressions)))
                   (error "Syntax error: 'else' should be at the end of a cond-expression")
                   (evaluate-sequence (cdr (car expressions)))))
              ((not (eq? (evaluate (car (car expressions))) #f))
               (evaluate-sequence (cdr (car expressions))))
              (else (cond-loop (cdr expressions)))))
      (splits-control-flow)
      (return-from-control-flow-split (cond-loop expressions)))
    
    (define (evaluate-define pattern . expressions)
      (if (symbol? pattern)
          (let* ((value (evaluate (car expressions)))
                 (binding (vector pattern value)))
            (set! environment (cons binding environment))
            value)
          (let* ((binding (vector (car pattern) '())))
            (set! environment (cons binding environment))
            (let* ((closure (close (cdr pattern) expressions (car pattern))))
              (vector-set! binding 1 closure)
              closure))))
    
    (define (evaluate-eval expression)
      (evaluate (evaluate expression)))
    
    (define (evaluate-if predicate consequent . alternate)
      (let* ((cond (evaluate predicate)))
        (splits-control-flow)
        (if cond
            (return-from-control-flow-split (thunkify consequent))
            (if (null? alternate)
                (return-from-control-flow-split '())
                (return-from-control-flow-split (thunkify (car alternate)))))))
    
    (define (evaluate-lambda parameters . expressions)
      (close parameters expressions "lambda"))
    
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
             (exp (read-port)))
        (close-input-port port)
        (evaluate (read port))))
    
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
    
    (define (actual-evaluate expression)
      
      (cond
        ((symbol? expression)
         (evaluate-variable expression))
        ((pair? expression)
         (let* ((operator (car expression))
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
                   (evaluate-application operator))) operands)))
        (else
         expression)))
    
    (set! evaluate actual-evaluate)
    
    (display output)
    (newline)
    (display ">>>")
    (loop (evaluate (read))))
  
  (loop "Slip"))