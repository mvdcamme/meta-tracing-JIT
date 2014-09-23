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

(define meta-level-apply apply)

(define list-of-expressions '())

(begin
  (define meta-level-eval eval)

;
; natives
;

  (define (wrap-native-procedure native-procedure)
    (lambda (arguments continue environment tailcall tracing?)
      (define native-value (meta-level-apply native-procedure arguments))
      (continue native-value environment tracing?)))

  (define (cps-apply expression continue environment tailcall tracing?)
    (define procedure (car expression))
    (define arguments (cadr expression))
    (procedure arguments continue environment tailcall tracing?))

  (define (cps-map expression continue environment tailcall tracing?)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items values)
      (if (null? items)
        (continue (reverse values) environment tracing?)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment tracing?)
            (iterate tail (cons value values)))
          (procedure (list head) continue-after-item environment #f tracing?))))
    (iterate items '()))

 (define (cps-for-each expression continue environment tailcall tracing?)
    (define procedure (car expression))
    (define items (cadr expression))
    (define (iterate items)
      (if (null? items)
        (continue '() environment tracing?)
        (let* ((head (car items))
              (tail (cdr items)))
          (define (continue-after-item value environment tracing?)
            (iterate tail))
          (procedure (list head) continue-after-item environment #f tracing?))))
    (iterate items))

  (define (cps-call-cc expression continue environment tailcall tracing?)
    (define procedure (car expression))
    (define (continuation arguments dynamic-continue dynamic-environment tailcall)
      (continue (car arguments) environment tracing?))
    (procedure (list continuation) continue environment tailcall tracing?))

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

    (define (evaluate-sequence expressions continue environment tailcall tracing?)
      (define head (car expressions))
      (define tail (cdr expressions))
      (define (continue-with-sequence value environment tracing?)
        (evaluate-sequence tail continue environment tailcall tracing?))
      (if (null? tail)
        (eval head continue environment tailcall tracing?)
        (eval head continue-with-sequence environment #f tracing?)))

    (define (make-procedure parameters expressions environment)
      (lambda (arguments continue dynamic-environment tailcall tracing?)
        (define (continue-after-sequence value environment-after-sequence tracing?)
          (continue value dynamic-environment tracing?))
        (define lexical-environment (bind-parameters parameters arguments environment))
        (if tailcall
          (evaluate-sequence expressions continue lexical-environment #t tracing?)
          (evaluate-sequence expressions continue-after-sequence lexical-environment #t tracing?))))

;
; evaluation functions
;

    (define (evaluate-application operator)
      (lambda operands
        (lambda (continue environment tailcall tracing?)
          (define (continue-after-operator procedure environment-after-operator tracing?)
            (define (evaluate-operands operands arguments environment)
              (define (continue-with-operands value environment-with-operands tracing?)
                (evaluate-operands (cdr operands) (cons value arguments) environment-with-operands))
              (if (null? operands)
                (procedure (reverse arguments) continue environment tailcall tracing?)
                (eval (car operands) continue-with-operands environment #f tracing?)))
            (evaluate-operands operands '() environment-after-operator))
          (if tracing?
              (begin (display "(")
                     (display operator)
                     (display " ")
                     (for-each (lambda (expression)
                                 (display expression) (display " " ))
                               operands)
                     (display ")")
                     (newline)))
          (eval operator continue-after-operator environment #f tracing?))))

    (define (evaluate-begin . expressions)
      (lambda (continue environment tailcall tracing?)
        (evaluate-sequence expressions continue environment tailcall tracing?)))
    
    (define (evaluate-can-start-loop expression)
      (lambda (continue environment tailcall tracing?)
        (define (continue-after-expression expression environment-after-continuation tracing?)
          (if (member expression list-of-expressions)
              (begin (display "looping!!!") (newline)
                     (continue '() environment #t))
              (begin (set! list-of-expressions (cons expression list-of-expressions))
                     (continue '() environment tracing?))))
        (display list-of-expressions) (newline)
        (display "number of distinct expressions: ") (display (length list-of-expressions)) (newline)
        (eval expression continue-after-expression environment tailcall tracing?)))
    
    (define (evaluate-cond . expressions)
      (lambda (continue environment tailcall tracing?)
        (define (evaluate-expressions expressions)
          (define (continue-after-predicate boolean environment-after-predicate tracing?)
            (if (eq? boolean #f)
                (evaluate-expressions (cdr expressions))
                (evaluate-sequence (cdar expressions) continue environment-after-predicate tailcall tracing?)))
          (cond ((null? expressions) (continue '() environment tracing?))
                ((eq? (caar expressions) 'else) (evaluate-sequence (cdar expressions) continue environment tailcall tracing?))
                (else (eval (caar expressions) continue-after-predicate environment #f tracing?))))
        (evaluate-expressions expressions)))

    (define (evaluate-define pattern . expressions)
      (lambda (continue environment tailcall tracing?)
        (define (continue-after-expression value environment-after-expression tracing?)
          (define binding (cons pattern value))
          (continue value (cons binding environment-after-expression) tracing?))
        (if (symbol? pattern)
          (eval (car expressions) continue-after-expression environment #f tracing?)
          (let* ((binding (cons (car pattern) '()))
                 (environment (cons binding environment))
                 (procedure (make-procedure (cdr pattern) expressions environment)))
              (set-cdr! binding procedure)
              (continue procedure environment tracing?)))))

    (define (evaluate-if predicate consequent . alternative) ;beware of guards
      (lambda (continue environment tailcall tracing?)
        (define (continue-after-predicate boolean environment-after-predicate tracing?)
          (if (eq? boolean #f) 
            (if (null? alternative)
              (continue '() environment-after-predicate tracing?)
              (eval (car alternative) continue environment-after-predicate tailcall tracing?))
            (eval consequent continue environment-after-predicate tailcall tracing?)))
        (eval predicate continue-after-predicate environment #f tracing?)))

    (define (evaluate-lambda parameters . expressions)
      (lambda (continue environment tailcall tracing?)
        (continue (make-procedure parameters expressions environment) environment tracing?)))
    
    (define (evaluate-let* . expressions)
      (lambda (continue environment tailcall tracing?)
        (let* ((bindings (car expressions))
               (body (cdr expressions)))
          (define (evaluate-bindings bindings environment)
            (define (continue-after-binding value environment-after-binding tracing?)
              (let* ((variable-name (caar bindings))
                     (binding (cons variable-name value))
                     (new-environment (cons binding environment)))
                (evaluate-bindings (cdr bindings) new-environment)))
            (if (null? bindings)
                (evaluate-sequence body continue environment tailcall tracing?)
                (eval (cadar bindings) continue-after-binding environment #f tracing?)))
          (evaluate-bindings bindings environment))))

    (define (evaluate-quote expression)
      (lambda (continue environment tailcall tracing?)
        (continue expression environment tracing?)))

    (define (evaluate-set! variable expression)
      (lambda (continue environment tailcall tracing?)
        (define (continue-after-expression value environment-after-expression tracing?)
          (define binding (assoc variable environment-after-expression))
          (if binding
            (set-cdr! binding value)
            (error "inaccessible variable: " variable))
          (continue value environment-after-expression tracing?))
        (eval expression continue-after-expression environment #f tracing?)))

    (define (evaluate-variable variable continue environment tracing?)
      (define binding (assoc variable environment))
      (cond (binding (continue (cdr binding) environment tracing?))
            (else (let* ((native-value (meta-level-eval variable (interaction-environment))))
                    (if (procedure? native-value)
                        (continue (wrap-native-procedure native-value) environment tracing?)
                        (continue native-value environment tracing?))))))

    (define (evaluate-while predicate . expressions)
      (lambda (continue environment tailcall tracing?)
        (define (iterate value environment)
          (define (continue-after-predicate boolean environment-after-predicate tracing?)
            (define (continue-after-sequence value environment-after-sequence tracing?)
              (iterate value environment))
            (if (eq? boolean #f)
              (continue value environment tracing?)
              (evaluate-sequence expressions continue-after-sequence environment #f tracing?)))
          (eval predicate continue-after-predicate environment #f tracing?))
        (iterate '() environment)))

;
; evaluator
;
  
    (define (evaluate expression continue environment tailcall tracing?)
      (cond
        ((symbol? expression)
         (evaluate-variable expression continue environment tracing?))
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
                   (else (evaluate-application operator))) operands) continue environment tailcall tracing?)))
        (else
          (continue expression environment tracing?))))

;
; read-eval-print
;
    
    (set! eval evaluate) 

    (display output)
    (newline)
    (display ">>>")
    (eval (read) loop environment #f #f))

  (loop "cpSlip* version 3" (list (cons 'apply    cps-apply   ) 
                                  (cons 'map      cps-map     ) 
                                  (cons 'for-each cps-for-each) 
                                  (cons 'call-cc  cps-call-cc ))))