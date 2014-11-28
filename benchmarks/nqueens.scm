(let ((__1-to0 
       (lambda (_n1) 
         (letrec ((_loop2 
                   (lambda (_i3 _l4) 
                     (let ((_p15 (= _i3 0))) 
                       (if _p15 
                           _l4 
                           (let ((_p16 (- _i3 1))) 
                             (let ((_p17 (cons _i3 _l4)))
                               (_loop2 _p16 _p17)))))))) 
           (_loop2 _n1 '()))))) 
  (letrec ((_ok?5 
            (lambda (_row6 _dist7 _placed8) 
              (let ((_p18 (null? _placed8))) 
                (if _p18 
                    #t 
                    (let ((_p19 (car _placed8))) 
                      (let ((_p20 (+ _row6 _dist7))) 
                        (let ((_p21 (= _p19 _p20))) 
                          (let ((_p22 (not _p21))) 
                            (if _p22 
                                (let ((_p23 (car _placed8))) 
                                  (let ((_p24 (- _row6 _dist7))) 
                                    (let ((_p25 (= _p23 _p24))) 
                                      (let ((_p26 (not _p25))) 
                                        (if _p26 
                                            (let ((_p27 (+ _dist7 1))) 
                                              (let ((_p28 (cdr _placed8))) 
                                                (_ok?5 _row6 _p27 _p28))) 
                                            #f))))) 
                                #f)))))))))) 
    (letrec ((_my-try9 (lambda (_x10 _y11 _z12) 
                         (let ((_p29 (null? _x10))) 
                           (if _p29 
                               (let ((_p30 (null? _y11))) 
                                 (if _p30 
                                     1 
                                     0)) 
                               (let ((_p31 (car _x10))) 
                                 (let ((_p32 (_ok?5 _p31 1 _z12))) 
                                   (let ((_p37 (if _p32 
                                                   (let ((_p33 (cdr _x10))) 
                                                     (let ((_p34 (append _p33 _y11)))
                                                       (let ((_p35 (car _x10))) 
                                                         (let ((_p36 (cons _p35 _z12)))
                                                           (_my-try9 _p34 '() _p36))))) 
                                                   0))) 
                                     (let ((_p38 (cdr _x10))) 
                                       (let ((_p39 (car _x10))) 
                                         (let ((_p40 (cons _p39 _y11))) 
                                           (let ((_p41 (_my-try9 _p38 _p40 _z12))) 
                                             (+ _p37 _p41))))))))))))) 
      (let ((_nqueens13 
             (lambda (_n14) 
               (let ((_p42 (__1-to0 _n14))) 
                 (_my-try9 _p42 '() '()))))) 
        (_nqueens13 4)))))