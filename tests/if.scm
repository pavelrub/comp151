(if (or #f #f)
  #f
  (or #f #t #f))

(if #t
  #t
  #f)

(if #f
  #t
  #f)

(if (or 
      (if #t
        #t
        #f)
      #f
      #f)
  #f
  #t)
