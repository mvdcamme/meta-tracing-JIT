(letrec ((even? (lambda (n) 
                  (let ((_1 (= n 0))) 
                    (if _1 
                        #t 
                        (let ((_2 (= n 1))) 
                          (if _2 
                              #f 
                              (let ((_3 (- n 2))) 
                                (let ((_4 (even? _3))) 
                                  _4))))))))) 
  (letrec ((div2* (lambda (n s) 
                    (let ((_5 (* 2 n))) 
                      (let ((_6 (= _5 s))) 
                        (if _6
                            n 
                            (let ((_7 (* 2 n))) 
                              (let ((_8 (+ _7 1))) 
                                (let ((_9 (= _8 s))) 
                                  (if _9 
                                      n 
                                      (let ((_10 (- n 1))) 
                                        (let ((_11 (div2* _10 s))) 
                                          _11)))))))))))) 
    (letrec ((div2 (lambda (n) 
                     (div2* n n)))) 
      (letrec ((hailstone* (lambda (n count) 
                             (let ((_12 (= n 1))) 
                               (if _12 
                                   count 
                                   (let ((_13 (even? n))) 
                                     (if _13 
                                         (let ((_14 (div2 n))) 
                                           (let ((_15 (+ count 1))) 
                                             (let ((_16 (hailstone* _14 _15))) 
                                               _16))) 
                                         (let ((_17 (* 3 n))) 
                                           (let ((_18 (+ _17 1))) 
                                             (let ((_19 (+ count 1))) 
                                               (let ((_20 (hailstone* _18 _19))) 
                                                 _20))))))))))) 
        (letrec ((hailstone (lambda (n) 
                              (hailstone* n 0)))) 
          (hailstone 5))))))
