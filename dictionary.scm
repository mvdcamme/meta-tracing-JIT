;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*                                                                 *-*-
;-*-*                Hash Tables (External Chaining)                  *-*-
;-*-*                                                                 *-*-
;-*-*                       Wolfgang De Meuter                        *-*-
;-*-*                 2008 Programming Technology Lab                 *-*-
;-*-*                   Vrije Universiteit Brussel                    *-*-
;-*-*                                                                 *-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
;-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-

(module dictionary racket
 (provide (rename-out (new new-dictionary))
          dictionary? insert! delete! find)
 
 (define make-assoc mcons)
 (define assoc-key mcar)
 (define assoc-value mcdr)
 
 (define dictionary-tag 'external-chaining) 
 (define (make ==? M h)
   (list dictionary-tag (make-vector M '()) h ==?))
 (define (storage table)
   (cadr table))
 (define (hash-function table)
   (caddr table))
 (define (equality table)
   (cadddr table))
 
 (define (new ==? M h)
   (make ==? M (lambda (k) (modulo (h k) M))))
 
 (define (dictionary? any)
   (and (pair? any)
        (eq? (car any) dictionary-tag)))
 
 (define (insert! table key val)
   (define vector (storage table))
   (define h (hash-function table))
   (define ==? (equality table))
   (define home-address (h key))
   (define assoc (make-assoc key val))
   (let insert-in-bucket 
     ((prev '())
      (next! (lambda (ignore next) 
               (vector-set! vector home-address next)))
      (next (vector-ref vector home-address)))
     (cond 
       ((null? next)
        (next! prev (mcons assoc next)))
       ((==? (assoc-key (mcar next)) key)
        (set-mcar! next assoc))
       (else
        (insert-in-bucket next set-mcdr! (mcdr next)))))
   table)
 
 (define (find table key)
   (define vector (storage table))
   (define h (hash-function table))
   (define ==? (equality table))
   (define home-address (h key))
   (let find-in-bucket 
     ((next (vector-ref vector home-address)))
     (cond
       ((null? next)
        #f)
       ((==? (assoc-key (mcar next)) key)
        (assoc-value (mcar next)))
       (else
        (find-in-bucket (mcdr next))))))
 
 (define (delete! table key)
   (define vector (storage table))
   (define h (hash-function table))
   (define ==? (equality table))
   (define home-address (h key))
   (let delete-from-bucket 
     ((prev '())
      (next! (lambda (ignore next) (vector-set! vector home-address next)))
      (next (vector-ref vector home-address)))
     (cond 
       ((null? next)
        #f)
       ((==? (assoc-key (mcar next)) key)
        (next! prev (mcdr next))
        table)
       (else
        (delete-from-bucket next set-mcdr! (mcdr next)))))
   table))