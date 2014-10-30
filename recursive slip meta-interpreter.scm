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
          (loop (cdr list) (cons (begin debug (f (car list)) acc)))))
    (loop lst '()))
  
  (define meta-circularity-level 0)
  
  (define environment '())
  
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
          (if (pair? parameters)
              (let* ((variable (car parameters))
                     (value (car arguments)))
                (bind-variable variable value)
                (bind-parameters (cdr parameters) (cdr arguments))))))
    
    (define (thunkify expression)
      (define frozen-environment environment)
      (define value (evaluate expression))
      (set! environment frozen-environment)
      value)
    
    (define (evaluate-sequence expressions)
      (define head (car expressions))
      (define tail (cdr expressions))
      (let* ((value (evaluate head)))
        (if (null? tail)
            value
            (evaluate-sequence tail))))
    
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
    
    (define (evaluate-application operator)
      (lambda operands
        (apply (evaluate operator) (map evaluate operands))))
    
    (define (evaluate-begin . expressions)
      (evaluate-sequence expressions))
    
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
      (if (evaluate predicate)
          (thunkify consequent)
          (if (null? alternate)
              '()
              (thunkify (car alternate)))))
    
    (define (evaluate-lambda parameters . expressions)
      (close parameters expressions))
    
    (define (evaluate-load string)
      (let* ((port (open-input-file string))
             (exp (read-port)))
        (close-input-port port)
        (evaluate (read port))))
    
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
          (eval variable (make-base-namespace))))
    
    (define (actual-evaluate expression)
      
      (cond
        ((symbol? expression)
         (evaluate-variable expression))
        ((pair? expression)
         (let* ((operator (car expression))
                (operands (cdr expression)))
           (apply
            (cond ((eq? operator 'begin)
                   evaluate-begin)
                  ((eq? operator 'define) 
                   evaluate-define)
                  ((eq? operator 'eval)
                   evaluate-eval)
                  ((eq? operator 'if) 
                   evaluate-if)
                  ((eq? operator 'lambda) 
                   evaluate-lambda)
                  ((eq? operator 'load) 
                   evaluate-load)
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