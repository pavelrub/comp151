(bin+ 3 4)
(bin+ 0 -12)
(bin- 0 8)
(bin- 5 3)
(bin* 5 3)
(bin* -20 -13)
(bin/ 8 4)
(bin/ 16 3)
(bin< 1 2)
(bin< 2 1)
(bin< 2 2)
(bin= 3 3)
(bin= 1 2)
(car (cons 1 2))
(cdr (cons 1 2))
(define x (cons 1 (cons 1 (cons 2 '()))))
(car x)
(cdr x)
(null? 5)
(null? '())
(define a (cons 1 2))
a
(pair? a)
(pair? 8)
(integer? a)
(integer? 10)
(procedure? cons)
(define a (lambda (x) x))
(procedure? a)
(procedure? 2)
(define b (cons 2 3))
b
(set-car! b 8)
b
(set-cdr! b 9)
b
(boolean? #f)
(boolean? 3)
(define a 'symbol)
(symbol->string a)
(string->symbol "test")
(string->symbol "test2")
'a
'b
'c
(string->symbol "check")
(string-ref "test" 1)
(string-length "test")
(char? #\a)
#\a
(string? "test-string")
(string? 123)
(symbol? 'a)
(symbol? 'kjahsdkjahsdkjahkjd)
(symbol? '(1 2 3))
(symbol? "bleh")
(char->integer #\a)