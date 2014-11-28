; CPS version of Gabriel benchmark tak

(letrec ((_tak0 (lambda (_x1 _y2 _z3 _k4) 
                  (let ((_p9 (< _y2 _x1))) 
                    (let ((_p10 (not _p9))) 
                      (if _p10 
                          (_k4 _z3) 
                          (let ((_p11 (- _x1 1))) 
                            (_tak0 _p11 _y2 _z3 
                                   (lambda (_v15) 
                                     (let ((_p12 (- _y2 1))) 
                                       (_tak0 _p12 _z3 _x1 
                                              (lambda (_v26) 
                                                (let ((_p13 (- _z3 1))) 
                                                  (_tak0 _p13 _x1 _y2 
                                                         (lambda (_v37) (_tak0 _v15 _v26 _v37 _k4))))))))))))))))
  (_tak0 8 4 2 (lambda (_a8) _a8)))
