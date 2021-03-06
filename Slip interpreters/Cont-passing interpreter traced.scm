;
; Slip: Lisp in 100 lines - Theo D'Hondt: SOFT: VUB - 2010
;
;       CPS* version
;
;       Version 3 - proper tail recursion
;                   
; <expression>  ::= <computation>|<lambda>|<quote>|<variable>|
;                   <literal>|<null> 
; <computation> ::= <definition>|<assignment>|<sequence>|
;                   <conditional>|<iteration>|<application>
; <definition>  ::= (define <variable> <expression>)
; <definition>  ::= (define <pattern> <expression>+)
; <assignment>  ::= (set! <variable> <expression>)
; <sequence>    ::= (begin <expression>+)
; <conditional> ::= (if <expression> <expression> <expression>)
; <conditional> ::= (if <expression> <expression>)
; <iteration>   ::= (while <expression> <expression>+)
; <application> ::= (<expression>+)
; <lambda>      ::= (lambda () <expression>+)
; <lambda>      ::= (lambda <variable> <expression>+)
; <lambda>      ::= (lambda (<pattern>) <expression>+)
; <quote>       ::= '[s-expression]
; <variable>    ::= [symbol]
; <pattern>     ::= (<variable>+)
; <pattern>     ::= (<variable>+ . <variable>)
; <literal>     ::= [number]|[character]|[string]|#t|#f
; <null>        ::= ()

; don't use syntactic constructs (e.g. cond, do, ...)

(begin

  (define meta-level-apply apply)
  (define meta-level-eval eval)
  
  (define (vassoc el list)
    (cond ((null? list) #f)
          ((eq? el (vector-ref (car list) 0)) (car list))
          (else (vassoc el (cdr list)))))

;
; natives
;

  (define (wrap-native-procedure native-procedure)
    (lambda (arguments continue environment tailcall)
      (define native-value (apply native-procedure arguments))
      (continue native-value environment)))

  (define (cps-apply expression continue environment tailcall)
    (define procedure (car expression))
    (define arguments (cadr expression))
    (procedure arguments continue environment tailcall))

  (define (cps-map expression continue environment tailcall)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items values)
      (if (null? items)
        (continue (reverse values) environment)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment)
            (iterate tail (cons value values)))
          (procedure (list head) continue-after-item environment #f))))
    (iterate items '()))

 (define (cps-for-each expression continue environment tailcall)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items)
      (if (null? items)
        (continue '() environment)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment)
            (iterate tail))
          (procedure (list head) continue-after-item environment #f))))
    (iterate items))

  (define (cps-call-cc expression continue environment tailcall)
    (define procedure (car expression))
    (define (continuation arguments dynamic-continue dynamic-environment tailcall)
      (continue (car arguments) environment))
    (procedure (list continuation) continue environment tailcall))

;
; read-eval-print
;

  (define (loop output environment)
    
    (define eval '())
    
    (define rollback environment)

    (define (error message qualifier)
      (display message)
      (loop qualifier rollback))

;
; functions
;

    (define (bind-variable variable value environment)
      (define binding (vector variable value))
      (cons binding environment))

    (define (bind-parameters parameters arguments environment)
      (if (symbol? parameters)
        (bind-variable parameters arguments environment)
        (if (pair? parameters)
          (let*
            ((variable (car parameters))
             (value (car arguments ))
             (environment (bind-variable variable value environment)))
            (bind-parameters (cdr parameters) (cdr arguments) environment))
          environment)))

    (define (evaluate-sequence expressions continue environment tailcall)
      (define head (car expressions))
      (define tail (cdr expressions))
      (define (continue-with-sequence value environment)
        (evaluate-sequence tail continue environment tailcall))
      (if (null? tail)
        (eval head continue environment tailcall)
        (eval head continue-with-sequence environment #f)))

    (define (make-procedure parameters expressions environment)
      (lambda (arguments continue dynamic-environment tailcall)
        (define (continue-after-sequence value environment-after-sequence)
          (can-close-loop expressions "some function")
          (continue value dynamic-environment))
        (define (continue-after-sequence-tail-recursive value environment-after-sequence)
          (can-close-loop expressions "some function")
          (continue value environment-after-sequence))
        (define lexical-environment (bind-parameters parameters arguments environment))
        (can-start-loop expressions "some function")
        (if tailcall
          (evaluate-sequence expressions continue lexical-environment #t)
          (evaluate-sequence expressions continue-after-sequence lexical-environment #t))))

;
; evaluation functions
;
    (define (evaluate-application operator)
      (lambda operands
        (lambda (continue environment tailcall)
          (define (continue-after-operator procedure environment-after-operator)
            (define (evaluate-operands operands arguments environment)
              (define (continue-with-operands value environment-with-operands)
                (evaluate-operands (cdr operands) (cons value arguments) environment-with-operands))
              (if (null? operands)
                  (procedure (reverse arguments) continue environment tailcall)
                  (eval (car operands) continue-with-operands environment #f)))
            (evaluate-operands operands '() environment-after-operator))
          (eval operator continue-after-operator environment #f))))

    (define (evaluate-begin . expressions)
      (lambda (continue environment tailcall)
        (evaluate-sequence expressions continue environment tailcall)))
    
    (define (evaluate-cond . expressions)
      (lambda (continue environment tailcall)
        (define (evaluate-expressions expressions)
          (define (continue-after-predicate boolean environment-after-predicate)
            (if (eq? boolean #f)
                (evaluate-expressions (cdr expressions))
                (evaluate-sequence (cdar expressions) continue environment-after-predicate tailcall)))
          (cond ((null? expressions) (continue '() environment))
                ((eq? (caar expressions) 'else) (evaluate-sequence (cdar expressions) continue environment tailcall))
                (else (eval (caar expressions) continue-after-predicate environment #f))))
        (evaluate-expressions expressions)))

    (define (evaluate-define pattern . expressions)
      (lambda (continue environment tailcall)
        (define (continue-after-expression value environment-after-expression)
          (define binding (vector pattern value))
          (continue value (cons binding environment-after-expression)))
        (if (symbol? pattern)
          (eval (car expressions) continue-after-expression environment #f)
          (let* ((binding (vector (car pattern) '()))
                 (environment (cons binding environment))
                 (procedure (make-procedure (cdr pattern) expressions environment)))
              (vector-set! binding 1 procedure)
              (continue procedure environment)))))

    (define (evaluate-if predicate consequent . alternative)
      (lambda (continue environment tailcall)
        (define (continue-after-predicate boolean environment-after-predicate)
          (if (eq? boolean #f) 
            (if (null? alternative)
              (continue '() environment-after-predicate)
              (eval (car alternative) continue environment-after-predicate tailcall))
            (eval consequent continue environment-after-predicate tailcall)))
        (eval predicate continue-after-predicate environment #f)))

    (define (evaluate-lambda parameters . expressions)
      (lambda (continue environment tailcall)
        (continue (make-procedure parameters expressions environment) environment)))
    
    (define (evaluate-let* . expressions)
      (lambda (continue environment tailcall)
        (let* ((bindings (car expressions))
               (body (cdr expressions)))
          (define (evaluate-bindings bindings environment)
            (define (continue-after-binding value environment-after-binding)
              (let* ((variable-name (caar bindings))
                     (binding (vector variable-name value))
                     (new-environment (cons binding environment)))
                (evaluate-bindings (cdr bindings) new-environment)))
            (if (null? bindings)
                (evaluate-sequence body continue environment tailcall)
                (eval (cadar bindings) continue-after-binding environment #f)))
          (evaluate-bindings bindings environment))))

    (define (evaluate-quote expression)
      (lambda (continue environment tailcall)
        (continue expression environment)))

    (define (evaluate-set! variable expression)
      (lambda (continue environment tailcall)
        (define (continue-after-expression value environment-after-expression)
          (define binding (vassoc variable environment-after-expression))
          (if binding
            (vector-set! binding 1 value)
            (error "inaccessible variable: " variable))
          (continue value environment-after-expression))
        (eval expression continue-after-expression environment #f)))
    
    (define (wrap-native-eval)
      (lambda (arguments continue environment tailcall)
        (define expression (car arguments))
        (define native-value (meta-level-eval expression (make-base-namespace)))
        (continue native-value environment)))

    (define (evaluate-variable variable continue environment)
      (define binding (vassoc variable environment))
      (cond (binding (continue (vector-ref binding 1) environment))
            (else (let* ((native-value (meta-level-eval variable (make-base-namespace))))
                    (if (procedure? native-value)
                        (continue (wrap-native-procedure native-value) environment)
                        (continue native-value environment))))))

    (define (evaluate-while predicate . expressions)
      (lambda (continue environment tailcall)
        (define (iterate value environment)
          (define (continue-after-predicate boolean environment-after-predicate)
            (define (continue-after-sequence value environment-after-sequence)
              (iterate value environment))
            (if (eq? boolean #f)
                (begin (can-close-loop expressions "while")
                       (continue value environment))
                (begin (can-start-loop expressions "while")
                       (evaluate-sequence expressions continue-after-sequence environment #f))))
          (eval predicate continue-after-predicate environment #f))
        (iterate '() environment)))

;
; evaluator
;
  
    (define (evaluate expression continue environment tailcall)
      (cond
        ((symbol? expression)
         (evaluate-variable expression continue environment))
        ((pair? expression)
         (let* ((operator (car expression))
               (operands (cdr expression)))
           ((apply
             (cond ((eq? operator 'begin) evaluate-begin)
                   ((eq? operator 'cond) evaluate-cond)
                   ((eq? operator 'define) evaluate-define)
                   ((eq? operator 'if) evaluate-if)
                   ((eq? operator 'lambda) evaluate-lambda)
                   ((eq? operator 'let*) evaluate-let*)
                   ((eq? operator 'quote) evaluate-quote)
                   ((eq? operator 'set!) evaluate-set!)
                   ((eq? operator 'while) evaluate-while)
                   (else (evaluate-application operator))) operands) continue environment tailcall)))
        (else
          (continue expression environment))))

;
; read-eval-print
;
    
    (set! eval evaluate) 

    (display output)
    (newline)
    (display ">>>")
    (eval (read) loop environment #f))

  (loop "cpSlip* version 3" (list (vector 'apply    cps-apply   ) 
                                  (vector 'map      cps-map     ) 
                                  (vector 'for-each cps-for-each) 
                                  (vector 'call-cc  cps-call-cc ))))