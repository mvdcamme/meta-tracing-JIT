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
  
  ;
  ;hashing
  ;
  
  (define (make-hash hash-size hash-fun comparison-fun)
    (define hash-vector (make-vector hash-size '()))
    (vector hash-vector hash-fun hash-size comparison-fun))
  
  (define (get-hash-vector hash)
    (vector-ref hash 0))
  
  (define (get-hash-fun hash)
    (vector-ref hash 1))
  
  (define (get-hash-size hash)
    (vector-ref hash 2))
  
  (define (get-comparison-fun hash)
    (vector-ref hash 3))
  
  (define make-assoc cons)
  (define get-key car)
  (define get-value cdr)
  
  (define (hash-get hash key)
    (let* ((comparison-fun (get-comparison-fun hash))
           (hash-fun (get-hash-fun hash))
           (hash-result (hash-fun key))
           (hash-vector (get-hash-vector hash)))
      (define (loop external-chain)
        (cond ((null? external-chain) #f)
              ((comparison-fun key (get-key (car external-chain))) (get-value (car external-chain)))
              (else (loop (cdr external-chain)))))
      (loop (vector-ref hash-vector hash-result))))
  
  (define (hash-set! hash key value)
    (let* ((assoc (make-assoc key value))
           (hash-fun (get-hash-fun hash))
           (hash-result (hash-fun key))
           (hash-vector (get-hash-vector hash)))
      (vector-set! hash-vector hash-result (cons assoc (vector-ref hash-vector hash-result)))))
  
  
  (define meta-level-eval eval)
  
  
  ;
  ;tracing
  ;
  
  (define (print s)
    (display s)
    (newline))
  
  (define (make-tracer-context function-call-stack should-trace? hash)
    (vector function-call-stack 
            should-trace?
            hash))
            
  (define (new-tracer-context)
    (make-tracer-context '() #f 
            (make-hash 10 (lambda (operator-name)
                            (define strg (symbol->string operator-name))
                            (define (loop i acc)
                              (if (>= i (string-length strg))
                                  (modulo acc 10)
                                  (loop (+ i 1) (+ acc (char->integer (string-ref strg i))))))
                            (loop 0 0))
                       eq?)))
  
  (define (get-function-call-stack tracer-context)
    (vector-ref tracer-context 0))
  
  (define (add-function-call procedure-name tracer-context)
    (make-tracer-context (cons procedure-name (get-function-call-stack tracer-context)) (should-trace? tracer-context) (get-number-of-function-calls-hash tracer-context)))
  
  (define (empty-function-call-stack? tracer-context)
    (null? (get-function-call-stack tracer-context)))
  
  (define (should-trace? tracer-context)
    (vector-ref tracer-context 1))
  
  (define (start-tracing tracer-context)
    (make-tracer-context (get-function-call-stack tracer-context) #t (get-number-of-function-calls-hash tracer-context)))
  
  (define (stop-tracing tracer-context)
    (make-tracer-context (get-function-call-stack tracer-context) #f (get-number-of-function-calls-hash tracer-context)))
  
  (define (get-number-of-function-calls-hash tracer-context)
    (vector-ref tracer-context 2))
  
  (define (get-number-of-function-calls operator-name tracer-context)
    (hash-get (get-number-of-function-calls-hash tracer-context) operator-name))
  
  (define (exists-function-call operator-name tracer-context)
    (if (hash-get (get-number-of-function-calls-hash tracer-context) operator-name)
        #t
        #f))
  
  (define (increment-number-of-function-calls! operator-name tracer-context)
    (set-number-of-function-calls! operator-name (+ (hash-get (get-number-of-function-calls-hash tracer-context) operator-name) 1) tracer-context))
  
  (define (decrement-number-of-function-calls! operator-name tracer-context)
    (set-number-of-function-calls! operator-name (- (hash-get (get-number-of-function-calls-hash tracer-context) operator-name) 1) tracer-context))
  
  (define (set-number-of-function-calls! operator-name value tracer-context)
    (hash-set! (get-number-of-function-calls-hash tracer-context) operator-name value))
  
  (define (print-if-tracing s tracer-context)
    (if (should-trace? tracer-context)
        (print s)))

;
; natives
;

  (define (wrap-native-procedure native-procedure)
    (lambda (arguments continue environment tailcall tracer-context)
      (print-if-tracing "wrap-native-procedure" tracer-context)
      (define native-value (apply native-procedure arguments))
      (continue native-value environment tracer-context)))

  (define (cps-apply expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define arguments (cadr expression))
    (print-if-tracing "cps-apply" tracer-context)
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
    (print-if-tracing "cps-map" tracer-context)
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
    (print-if-tracing "cps-for-each" tracer-context)
    (iterate items))

  (define (cps-call-cc expression continue environment tailcall tracer-context)
    (define procedure (car expression))
    (define (continuation arguments dynamic-continue dynamic-environment tailcall tracer-context)
      (continue (car arguments) environment tracer-context))
    (print-if-tracing "cps-call-cc" )
    (procedure (list continuation) continue environment tailcall tracer-context))

;
; read-eval-print
;

  (define (loop output environment tracer-context)
    (define rollback environment)

    (define (error message qualifier)
      (display message)
      (loop qualifier rollback))

;
; functions
;

    (define (bind-variable variable value environment)
      (define binding (cons variable value))
      (print-if-tracing "bind-variable" tracer-context)
      (cons binding environment))

    (define (bind-parameters parameters arguments environment)
      (print-if-tracing "bind-parameters" tracer-context)
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
      (print-if-tracing "evaluate-sequence" tracer-context)
      (if (null? tail)
        (eval head continue environment tailcall tracer-context)
        (eval head continue-with-sequence environment #f tracer-context)))

    (define (make-procedure parameters expressions environment lexical-tracer-context)
      (print-if-tracing "make-procedure" lexical-tracer-context)
      (lambda (arguments continue dynamic-environment tailcall dynamic-tracer-context)
        (define (continue-after-sequence value environment-after-sequence tracer-context)
          (continue value dynamic-environment tracer-context))
        (define lexical-environment (bind-parameters parameters arguments environment))
        (display "in make-procedure, ") (print dynamic-tracer-context)
        (if tailcall
          (evaluate-sequence expressions continue lexical-environment #t dynamic-tracer-context)
          (evaluate-sequence expressions continue-after-sequence lexical-environment #t dynamic-tracer-context))))

;
; evaluation functions
;
    
    (define (is-recursable-function? operator environment)
      (if (symbol? operator)  ;Can't use 'and' here because it's a special form in Racket
          (assoc operator environment)
          #f))
    
    (define (is-looping? function-call-stack)
      (if (null? function-call-stack)
          #f
          (or (member (car function-call-stack) (cdr function-call-stack))
              (is-looping? (cdr function-call-stack)))))

    (define (evaluate-application operator)
      (lambda operands
        (lambda (continue environment tailcall tracer-context)
          (define (continue-after-recursable-operator procedure environment-after-operator tracer-context)
            (define (evaluate-operands operands arguments environment)
              (define (continue-with-operands value environment-with-operands tracer-context)
                (evaluate-operands (cdr operands) (cons value arguments) environment-with-operands))
              (display "in evaluate-operands: ") (print tracer-context)
              (if (null? operands)
                  (procedure (reverse arguments) continue environment tailcall (let* ((base-tracer-context (add-function-call operator tracer-context)))
                                                                                 (if (> (get-number-of-function-calls operator tracer-context) 3)
                                                                                     (start-tracing base-tracer-context)
                                                                                     base-tracer-context)))
                  (eval (car operands) continue-with-operands environment #f (add-function-call operator tracer-context))))
            (if (exists-function-call operator tracer-context)
                (increment-number-of-function-calls! operator tracer-context)
                (set-number-of-function-calls! operator 1 tracer-context))
            (if (is-looping? (get-function-call-stack tracer-context))
                (begin (display "looping!")
                       (newline)))
            (display operator) (display " -> ") (print tracer-context)
            (evaluate-operands operands '() environment-after-operator))
          (define (continue-after-non-recursable-operator procedure environment-after-operator tracer-context)
            (define (evaluate-operands operands arguments environment)
              (define (continue-with-operands value environment-with-operands tracer-context)
                (evaluate-operands (cdr operands) (cons value arguments) environment-with-operands))
              (if (null? operands)
                  (procedure (reverse arguments) continue environment tailcall tracer-context)
                  (eval (car operands) continue-with-operands environment #f tracer-context)))
            (evaluate-operands operands '() environment-after-operator))
          (print-if-tracing "evaluate-application" tracer-context)
          (eval operator (if (is-recursable-function? operator environment)
                                 continue-after-recursable-operator
                                 continue-after-non-recursable-operator)
                    environment #f tracer-context))))
            

    (define (evaluate-begin . expressions)
      (lambda (continue environment tailcall tracer-context)
        (print-if-tracing "evaluate-begin" tracer-context)
        (evaluate-sequence expressions continue environment tailcall tracer-context)))
    
    (define (evaluate-cond . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (evaluate-expressions expressions)
          (define (continue-after-predicate boolean environment-after-predicate tracer-context)
            (if (eq? boolean #t)
                (evaluate-sequence (cdar expressions) continue environment-after-predicate tailcall tracer-context)
                (evaluate-expressions (cdr expressions))))
          (cond ((null? expressions) (continue '() environment tracer-context))
                ((eq? (caar expressions) 'else) (evaluate-sequence (cdar expressions) continue environment tailcall tracer-context))
                (else (eval (caar expressions) continue-after-predicate environment #f tracer-context))))
        (print-if-tracing "evaluate-cond" tracer-context)
        (evaluate-expressions expressions)))

    (define (evaluate-define pattern . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-expression value environment-after-expression tracer-context)
          (define binding (cons pattern value))
          (continue value (cons binding environment-after-expression) tracer-context))
        (print-if-tracing "evaluate-define" tracer-context)
        (if (symbol? pattern)
            (eval (car expressions) continue-after-expression environment #f tracer-context)
            (let* ((binding (cons (car pattern) '()))
                   (environment (cons binding environment))
                   (procedure (make-procedure (cdr pattern) expressions environment tracer-context)))
              (set-cdr! binding procedure)
              (continue procedure environment tracer-context)))))

    (define (evaluate-if predicate consequent . alternative)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-predicate boolean environment-after-predicate tracer-context)
          (if (eq? boolean #f) 
            (if (null? alternative)
              (continue '() environment-after-predicate tracer-context)
              (eval (car alternative) continue environment-after-predicate tailcall tracer-context))
            (eval consequent continue environment-after-predicate tailcall tracer-context)))
        (print-if-tracing "evaluate-if" tracer-context)
        (eval predicate continue-after-predicate environment #f tracer-context)))

    (define (evaluate-lambda parameters . expressions)
      (lambda (continue environment tailcall tracer-context)
        (continue (make-procedure parameters expressions environment tracer-context) environment tracer-context)))
    
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
        (print-if-tracing "evaluate-quote" tracer-context)
        (continue expression environment tracer-context)))

    (define (evaluate-set! variable expression)
      (lambda (continue environment tailcall tracer-context)
        (define (continue-after-expression value environment-after-expression tracer-context)
          (define binding (assoc variable environment-after-expression))
          (if binding
            (set-cdr! binding value)
            (error "inaccessible variable: " variable))
          (continue value environment-after-expression tracer-context))
        (print-if-tracing "evaluate-set!" tracer-context)
        (eval expression continue-after-expression environment #f tracer-context)))

    (define (evaluate-variable variable continue environment tracer-context)
      (define binding (assoc variable environment))
      (print-if-tracing "evaluate-variable" tracer-context)
      (if binding
          (continue (cdr binding) environment tracer-context)
          (let* ((native-value (meta-level-eval variable (interaction-environment))))
            (if (procedure? native-value)
                (continue (wrap-native-procedure native-value) environment tracer-context)
                (continue native-value environment tracer-context)))))

    (define (evaluate-while predicate . expressions)
      (lambda (continue environment tailcall tracer-context)
        (define (iterate value environment tracer-context)
          (define (continue-after-predicate boolean environment-after-predicate tracer-context)
            (define (continue-after-sequence value environment-after-sequence tracer-context)
              (iterate value environment tracer-context))
            (if (eq? boolean #f)
              (continue value environment tracer-context)
              (evaluate-sequence expressions continue-after-sequence environment #f tracer-context)))
          (eval predicate continue-after-predicate environment #f tracer-context))
        (print-if-tracing "evaluate-while" tracer-context)
        (iterate '() environment tracer-context)))

;
; evaluator
;
  
    (define (eval expression continue environment tailcall tracer-context)
      (print-if-tracing "evaluate" tracer-context)
      (cond ((symbol? expression) (evaluate-variable expression continue environment tracer-context))
            ((pair? expression)
             (define operator (car expression))
             (define operands (cdr expression))
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
                     (else (evaluate-application operator))) operands) continue environment tailcall tracer-context))
            (else (continue expression environment tracer-context))))

;
; read-eval-print
;

    (display output)
    (newline)
    (display ">>>")
    (eval (read) loop environment #f (new-tracer-context)))

  (loop "cpSlip* version 3"
        (list (cons 'apply    cps-apply   ) 
              (cons 'map      cps-map     ) 
              (cons 'for-each cps-for-each) 
              (cons 'call-cc  cps-call-cc ))
        (new-tracer-context)))