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

;(define (fac x) (if (< x 2) 1 (* x (fac (- x 1)))))

(define meta-level-apply apply)

(define list-of-expressions '())

(define a-procedure #f)

(begin
  (define meta-level-eval eval)
  
;  
;tracing-context
;
  
  (define (make-tracer-context is-tracing? expression-to-be-traced expressions-already-traced)
    (vector is-tracing? expression-to-be-traced expressions-already-traced))
            
  (define (new-tracer-context)
    (make-tracer-context #f #f '()))
  
  (define (is-tracing? tracer-context)
    (vector-ref tracer-context 0))
  
  (define (is-tracing-expression? tracer-context expression)
    (eq? (vector-ref tracer-context 1) expression))
  
  (define (start-tracing-expression! tracer-context expression)
    (vector-set! tracer-context 0 #t)
    (vector-set! tracer-context 1 expression))
  
  (define (stop-tracing! tracer-context)
    (vector-set! tracer-context 2 (cons (vector-ref tracer-context 1) (vector-ref tracer-context 2)))
    (vector-set! tracer-context 0 #f)
    (vector-set! tracer-context 1 #f))
  
  (define (is-expression-traced? tracer-context expression)
    (member expression (vector-ref tracer-context 2)))
  
  (define (add-expression-traced! tracer-context expression)
    (vector-set! tracer-context 2 (cons expression (vector-ref tracer-context 2))))
  
;
; natives
;

  (define (wrap-native-procedure native-procedure)
    (lambda (arguments continue environment tailcall tracer-context)
      (let* ((native-value (meta-level-apply native-procedure arguments)))
          (if (is-tracing? tracer-context)
              (begin (display "(")
                     (display native-procedure)
                     (for-each (lambda (argument)
                                 (display " " ) (display argument))
                               arguments)
                     (display ")")
                     (newline)))
        (continue native-value environment tracer-context))))

  (define (cps-apply expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define arguments (cadr expression))
    (procedure arguments continue environment tailcall tracer-context))

  (define (cps-map expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items values)
      (if (null? items)
        (continue (reverse values) environment tracer-context)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment tracer-context)
            (iterate tail (cons value values)))
          (procedure (list head) continue-after-item environment #f tracer-context))))
    (iterate items '()))

 (define (cps-for-each expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items)
      (if (null? items)
        (continue '() environment tracer-context)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment tracer-context)
            (iterate tail))
          (procedure (list head) continue-after-item environment #f tracer-context))))
    (iterate items))

  (define (cps-call-cc expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define (continuation arguments dynamic-continue dynamic-environment tailcall)
      (continue (car arguments) environment tracer-context))
    (procedure (list continuation) continue environment tailcall tracer-context))

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
      (define binding (cons variable value))
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

    (define (evaluate-sequence expressions continue environment tailcall tracer-context)
      (define head (car expressions))
      (define tail (cdr expressions))
      (define (continue-with-sequence value environment tracer-context)
        (evaluate-sequence tail continue environment tailcall tracer-context))
      (if (null? tail)
        (eval head continue environment tailcall tracer-context)
        (eval head continue-with-sequence environment #f tracer-context)))

    (define (make-procedure parameters expressions environment)
      (lambda (arguments continue dynamic-environment tailcall tracer-context)
        (define (continue-after-sequence value environment-after-sequence tracer-context)
          (continue value dynamic-environment tracer-context))
        (define lexical-environment (bind-parameters parameters arguments environment))
        (if tailcall
          (evaluate-sequence expressions continue lexical-environment #t tracer-context)
          (evaluate-sequence expressions continue-after-sequence lexical-environment #t tracer-context))))

;
; evaluation functions
;

    (define (evaluate-application operator)
      (lambda operands
        (lambda (continue environment tailcall tracer-context)
          (define (continue-after-operator procedure environment-after-operator tracer-context)
            (define (evaluate-operands operands arguments environment)
              (define (continue-with-operands value environment-with-operands tracer-context)
                (evaluate-operands (cdr operands) (cons value arguments) environment-with-operands))
              (if (null? operands)
                (procedure (reverse arguments) continue environment tailcall tracer-context)
                (eval (car operands) continue-with-operands environment #f tracer-context)))
            (if (not a-procedure)
                (set! a-procedure procedure))
            (evaluate-operands operands '() environment-after-operator))
          (eval operator continue-after-operator environment #f tracer-context))))

    (define (evaluate-begin . expressions)
      (lambda (continue environment tailcall tracer-context)
        (evaluate-sequence expressions continue environment tailcall tracer-context)))
    
    (define (evaluate-can-start-loop expression)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-expression expression environment-after-continuation tracer-context)
          (cond ((is-expression-traced? tracer-context expression) (display "expression already traced!") (newline))
                ((is-tracing-expression? tracer-context expression) (display "stop looping!") (newline) (stop-tracing! tracer-context))
                ((member expression list-of-expressions) (display "looping!") (newline) (start-tracing-expression! tracer-context expression))
                (else (set! list-of-expressions (cons expression list-of-expressions))))
          (continue '() environment tracer-context))
        (display list-of-expressions) (newline)
        (display "number of distinct expressions: ") (display (length list-of-expressions)) (newline)
        (eval expression continue-after-expression environment tailcall tracer-context)))
    
    (define (evaluate-cond . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (evaluate-expressions expressions)
          (define (continue-after-predicate boolean environment-after-predicate tracer-context)
            (if (eq? boolean #f)
                (evaluate-expressions (cdr expressions))
                (evaluate-sequence (cdar expressions) continue environment-after-predicate tailcall tracer-context)))
          (cond ((null? expressions) (continue '() environment tracer-context))
                ((eq? (caar expressions) 'else) (evaluate-sequence (cdar expressions) continue environment tailcall tracer-context))
                (else (eval (caar expressions) continue-after-predicate environment #f tracer-context))))
        (evaluate-expressions expressions)))

    (define (evaluate-define pattern . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-expression value environment-after-expression tracer-context)
          (define binding (cons pattern value))
          (continue value (cons binding environment-after-expression) tracer-context))
        (if (symbol? pattern)
          (eval (car expressions) continue-after-expression environment #f tracer-context)
          (let* ((binding (cons (car pattern) '()))
                 (environment (cons binding environment))
                 (procedure (make-procedure (cdr pattern) expressions environment)))
              (set-cdr! binding procedure)
              (continue procedure environment tracer-context)))))

    (define (evaluate-if predicate consequent . alternative) ;beware of guards
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-predicate boolean environment-after-predicate tracer-context)
          (if (eq? boolean #f) 
            (if (null? alternative)
              (continue '() environment-after-predicate tracer-context)
              (eval (car alternative) continue environment-after-predicate tailcall tracer-context))
            (eval consequent continue environment-after-predicate tailcall tracer-context)))
        (eval predicate continue-after-predicate environment #f tracer-context)))

    (define (evaluate-lambda parameters . expressions)
      (lambda (continue environment tailcall tracer-context)
        (continue (make-procedure parameters expressions environment) environment tracer-context)))
    
    (define (evaluate-let* . expressions)
      (lambda (continue environment tailcall tracer-context)
        (let* ((bindings (car expressions))
               (body (cdr expressions)))
          (define (evaluate-bindings bindings environment)
            (define (continue-after-binding value environment-after-binding tracer-context)
              (let* ((variable-name (caar bindings))
                     (binding (cons variable-name value))
                     (new-environment (cons binding environment)))
                (evaluate-bindings (cdr bindings) new-environment)))
            (if (null? bindings)
                (evaluate-sequence body continue environment tailcall tracer-context)
                (eval (cadar bindings) continue-after-binding environment #f tracer-context)))
          (evaluate-bindings bindings environment))))

    (define (evaluate-quote expression)
      (lambda (continue environment tailcall tracer-context)
        (continue expression environment tracer-context)))

    (define (evaluate-set! variable expression)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-expression value environment-after-expression tracer-context)
          (define binding (assoc variable environment-after-expression))
          (if binding
            (set-cdr! binding value)
            (error "inaccessible variable: " variable))
          (continue value environment-after-expression tracer-context))
        (eval expression continue-after-expression environment #f tracer-context)))

    (define (evaluate-variable variable continue environment tracer-context)
      (define binding (assoc variable environment))
      (cond (binding (continue (cdr binding) environment tracer-context))
            (else (let* ((native-value (meta-level-eval variable (interaction-environment))))
                    (if (procedure? native-value)
                        (continue (wrap-native-procedure native-value) environment tracer-context)
                        (continue native-value environment tracer-context))))))

    (define (evaluate-while predicate . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (iterate value environment)
          (define (continue-after-predicate boolean environment-after-predicate tracer-context)
            (define (continue-after-sequence value environment-after-sequence tracer-context)
              (iterate value environment))
            (if (eq? boolean #f)
              (continue value environment tracer-context)
              (evaluate-sequence expressions continue-after-sequence environment #f tracer-context)))
          (eval predicate continue-after-predicate environment #f tracer-context))
        (iterate '() environment)))

;
; evaluator
;
  
    (define (evaluate expression continue environment tailcall tracer-context)
      (cond
        ((symbol? expression)
         (evaluate-variable expression continue environment tracer-context))
        ((pair? expression)
         (let* ((operator (car expression))
               (operands (cdr expression)))
           ((apply
             (cond ((eq? operator 'begin) evaluate-begin)
                   ((eq? operator 'can-start-loop) evaluate-can-start-loop)
                   ((eq? operator 'cond) evaluate-cond)
                   ((eq? operator 'define) evaluate-define)
                   ((eq? operator 'if) evaluate-if)
                   ((eq? operator 'lambda) evaluate-lambda)
                   ((eq? operator 'let*) evaluate-let*)
                   ((eq? operator 'quote) evaluate-quote)
                   ((eq? operator 'set!) evaluate-set!)
                   ((eq? operator 'while) evaluate-while)
                   (else (evaluate-application operator))) operands) continue environment tailcall tracer-context)))
        (else
          (continue expression environment tracer-context))))

;
; read-eval-print
;
    
    (set! eval evaluate) 

    (display output)
    (newline)
    (display ">>>")
    (eval (read) loop environment #f (new-tracer-context)))

  (loop "cpSlip* version 3" (list (cons 'apply    cps-apply   ) 
                                  (cons 'map      cps-map     ) 
                                  (cons 'for-each cps-for-each) 
                                  (cons 'call-cc  cps-call-cc ))))