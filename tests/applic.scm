((lambda (x y) (or x y)) #f #t)
((lambda (x y z) (or x y (and x y z))) ((lambda (x) (or x x)) (and #f #t))
                                       #f
                                       #t)
