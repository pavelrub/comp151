((lambda ()
   ((lambda () #f))))

((lambda ()
   ((lambda (a) #t) #t)))

((lambda (a b)
   ((lambda (a) b) #t)) #f #t)

((lambda (a)
   ((lambda () 
      ((lambda () a))))) #f )

((lambda (a)
   ((lambda () 
      (or ((lambda () a)) #f)))) #f )

((lambda (x)
   (x #f #t #f))
 (lambda (a b c)
   (or a b c)))
