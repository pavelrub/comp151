(load "pattern-matcher.scm")

(print-graph #f) ; display circular structures
(print-gensym #f) ; print gensym as g1234
(case-sensitive #f) ; ditto
(print-brackets #f) ; do not use brackets when pretty-printing
(revert-interaction-semantics) ; allow builtins to be redefined

;;; fix bug in optimizer
(#%$sputprop 'append '*flags* 122)
(#%$sputprop 'append! '*flags* 34)
(#%$sputprop 'list* '*flags* 1250)
(#%$sputprop 'cons* '*flags* 1250)

;;; And just for good luck :-)
(define with (lambda (s f) (apply f s)))

(define simple-const?
  (lambda (x)
    (or (boolean? x) (char? x) (number? x) (string? x))))

(define *reserved-words*
  '(and begin cond define do else if lambda
        let let* letrec or quasiquote unquote
        unquote-splicing quote set!))

(define not-reserved-word?
  (lambda (x)
    (if (memq x *reserved-words*)
        #f
        #t)))

(define var?
  (lambda (x)
    (not (or (memq x *reserved-words*)
             (pair? x)
             (list? x)))))


(define beginify
  (lambda (a)
    (cond ((null? a) (if #f #f))
          ((null? (cdr a)) (car a))
          (else `(begin ,@a)))))

(define *void-object* (if #f #f))

(define void?
  (lambda (e)
    (eq? e *void-object*)))

(define list-of-vars?
  (lambda (x)
    (and
     (list? x)
     (andmap var? x))))
(define improper-list?
  (lambda (x)
    (and (pair? x) (not (list? x)))))

(define last
  (lambda (lst)
    (cond ((not (pair? lst)) lst)
          (else (last (cdr lst))))))

(define all-but-last
  (lambda (lst)
    (cond ((pair? lst) (cons (car lst) (all-but-last (cdr lst))))
          (else '()))))

(define improper-list-of-vars?
  (lambda (x)
    (and
     (improper-list? x)
     (var? (last x))
     (list-of-vars? (all-but-last x)))))

(define has-duplicates?
  (lambda (l)
    (cond ((null? l) #f)
          ((member (car l) (cdr l)) #t)
          (else (has-duplicates? (cdr l))))))

(define unique-cars?
  (lambda (l)
    (let ((cars (map car l)))
      (not (has-duplicates? cars)))))

(define with
  (lambda (s f)
    (apply f s)))

(define Ym
  (lambda fs
    (let ((ms (map
               (lambda (fi)
                 (lambda ms
                   (apply fi (map (lambda (mi)
                                    (lambda args
                                      (apply (apply mi ms) args))) ms))))
               fs)))
      (apply (car ms) ms))))

(define expand-letrec
  (lambda (letrec-expr)
    (with letrec-expr
          (lambda (_letrec ribs . exprs)
            (let* ((fs (map car ribs))
                   (lambda-exprs (map cdr ribs))
                   (nu (gensym))
                   (nu+fs `(,nu ,@fs))
                   (body-f `(lambda ,nu+fs ,@exprs))
                   (hofs
                    (map (lambda (lambda-expr) `(lambda ,nu+fs ,@lambda-expr))
                         lambda-exprs)))
              `(Ym ,body-f ,@hofs))))))

(define letrec?
  (lambda (expr)
    (and (pair? expr) (eq? (car expr) 'letrec))))

(define expand-and
  (lambda (and-expr)
    `(if ,(car and-expr) ,(expand-and (cdr and-expr) '#f))))

(define expand-qq
  (lambda (e)
    (cond ((unquote? e) (cadr e))
          ((unquote-splicing? e)
           (error 'expand-qq "unquote-splicing here makes no sense!"))
          ((pair? e)
           (let ((a (car e))
                 (b (cdr e)))
             (cond ((unquote-splicing? a) `(append ,(cadr a) ,(expand-qq b)))
                   ((unquote-splicing? b) `(cons ,(expand-qq a) ,(cadr b)))
                   (else `(cons ,(expand-qq a) ,(expand-qq b))))))
          ((vector? e) `(list->vector ,(expand-qq (vector->list e))))
          ((or (null? e) (symbol? e)) `',e)
          (else e))))

(define ^quote?
  (lambda (tag)
    (lambda (e)
      (and (pair? e)
           (eq? (car e) tag)
           (pair? (cdr e))
           (null? (cddr e))))))

(define unquote? (^quote? 'unquote))
(define unquote-splicing? (^quote? 'unquote-splicing))

(define parse
  (let ((run
         (compose-patterns
          (pattern-rule
           (? 'c simple-const?)
           (lambda (c) `(const ,c)))
          (pattern-rule
           `(quote ,(? 'c))
           (lambda (c) `(const ,c)))
          (pattern-rule
           (? 'v var?)
           (lambda (v) `(var ,v)))
          (pattern-rule
           `(if ,(? 'test) ,(? 'dit))
           (lambda (test dit)
             `(if3 ,(parse test) ,(parse dit) (const ,*void-object*))))
          (pattern-rule
           `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
           (lambda (test dit dif)
             `(if3 ,(parse test) ,(parse dit) ,(parse dif))))
          (pattern-rule
           `(lambda ,(? 'args list-of-vars?) . ,(? 'body))
           (lambda (args body)
             `(lambda-simple ,args ,(parse (beginify body)))))
          (pattern-rule
           `(lambda ,(? 'args improper-list-of-vars?) . ,(? 'body))
           (lambda (args body)
             `(lambda-opt ,(all-but-last args) ,(last args) ,(parse (beginify body)))))
          (pattern-rule
           `(lambda ,(? 'args var?) . ,(? 'body))
           (lambda (args body)
             `(lambda-variadic ,args ,(parse (beginify body)))))
          (pattern-rule
           `(define ,(? 'var var?) ,(? 'expr))
           (lambda (v expr)
             `(define ,(parse v) ,(parse expr))))
          (pattern-rule
           `(define ,(? 'vars pair?) ,(? 'expr))
           (lambda (vars expr)
             `(define ,(parse (car vars)) ,(parse `(lambda ,(cdr vars) ,expr)))))
          (pattern-rule
           `(begin . ,(? 'lst list?))
           (lambda (lst)
             `(seq ,(map parse lst))))
          (pattern-rule
           `(,(? 'e1 not-reserved-word?) . ,(? 'args list?))
           (lambda (e1 args)
             `(applic ,(parse e1) ,(map parse args))))
          (pattern-rule
           `(or)
           (lambda ()
             (parse '#f)))
          (pattern-rule
           `(or ,(? 'expr))
           (lambda (expr)
             (parse expr)))
          (pattern-rule
           `(or . ,(? 'exprs))
           (lambda (exprs)
             `(or ,(map parse exprs))))
          (pattern-rule
           `(and)
           (lambda ()
             (parse '#t)))
          (pattern-rule
           `(and ,(? 'expr))
           (lambda (expr)
             (parse expr)))
          (pattern-rule
           `(and ,(? 'expr1) ,(? 'expr2))
           (lambda (expr1 expr2)
             (parse `(if ,expr1 ,expr2 #f))))
          (pattern-rule
          `(and ,(? 'expr) . ,(? 'rest))
           (lambda (expr rest)
             (parse `(if ,expr (and ,@rest) #f))))
          (pattern-rule
           `(let ,(? 'vars unique-cars?) . ,(? 'exprs))
           (lambda (vars exprs)
             (parse
              `((lambda ,(map car vars) ,@exprs) ,@(map cadr vars)))))
          (pattern-rule
           `(let* () ,(? 'expr) . ,(? 'exprs list?))
           (lambda (expr exprs)
             (parse (beginify (cons expr exprs)))))
          (pattern-rule
           `(let* ((,(? 'var var?) ,(? 'val)) . ,(? 'rest)) . ,(? 'exprs))
           (lambda (var val rest exprs)
             (parse `(let ((,var ,val))
                       (let* ,rest . ,exprs)))))
          (pattern-rule
           (? 'expr letrec?)
           (lambda (expr)
             (parse (expand-letrec `,expr))))
          (pattern-rule
           `(cond)
           (lambda ()
             `(const ,*void-object*)))
          (pattern-rule
           `(cond (else . ,(? 'exprs)))
           (lambda (exprs)
             (parse (beginify exprs))))
          (pattern-rule
           `(cond (,(? 't1) . ,(? 't1-rest)) . ,(? 'rest))
           (lambda (t1 t1-rest rest)
             (parse `(if ,t1 ,(beginify t1-rest) (cond ,@rest)))))
          (pattern-rule
           (list 'quasiquote (? 'sexpr))
           (lambda (sexpr)
             (parse (expand-qq sexpr))))
          )))
    (lambda (e)
      (run e
           (lambda ()
             (error 'parse
                    (format "I can't recognize this: ~s" e)))))))

(define get-minor-acc
  (lambda (var var-list minor)
    (cond ((null? var-list) -1)
          ((eq? (car var-list) var) minor)
          (else (get-minor-acc var (cdr var-list) (+ minor 1))))))

(define get-minor
  (lambda (var var-list)
    (get-minor-acc var var-list 0)))

(define get-major-minor-acc
  (lambda (var vars-mat major)
    (if (null? vars-mat)
        (list -1 -1)
        (let ((minor (get-minor var (car vars-mat))))
          (if (> minor -1)
              (list major minor)
              (get-major-minor-acc var (cdr vars-mat) (+ 1 major)))))))

(define get-major-minor
  (lambda (var vars-mat)
    (get-major-minor-acc var vars-mat 0)))

(define var->lex-var
  (lambda (var pvars bvars)
    (let ((pvar-index (get-minor var pvars)))
      (if (> pvar-index -1)
          `(pvar ,var ,pvar-index)
          (let ((bvar-indexes (get-major-minor var bvars)))
            (if (> (car bvar-indexes) -1)
                `(bvar ,var ,@bvar-indexes)
                `(fvar ,var)))))))

(define get-tag
  (lambda (l)
    (if (list?  l)
        (car l)
        'error)))

(define is-simple-lambda?
  (lambda (exp)
    (eq? (get-tag exp) 'lambda-simple)))

(define get-lambda-simple-params
  (lambda (lambda-exp)
    (cadr lambda-exp)))

(define get-lambda-simple-body
  (lambda (lambda-exp)
    (caddr lambda-exp)))

(define is-opt-lambda?
  (lambda (exp)
    (eq? (get-tag exp) 'lambda-opt)))

(define get-lambda-opt-params
  (lambda (exp)
    (append (cadr exp) (list (caddr exp)))))

(define get-lambda-opt-body
  (lambda (exp)
    (cadddr exp)))

(define is-var-lambda?
  (lambda (exp)
    (eq? (get-tag exp) 'lambda-variadic)))

(define get-lambda-var-params
  (lambda (exp)
    (list (cadr exp))))

(define get-lambda-var-body
  (lambda (exp)
    (caddr exp)))

(define get-last
  (lambda (l)
    (car (reverse l))))

(define get-all-but-last
  (lambda (l)
    (reverse (cdr (reverse l)))))

(define pe->lex-pe*
  (lambda (exp pvars bvars)
    (cond ((null? exp) '())
          ((not (list? exp)) exp)
          ((is-simple-lambda? exp)
           (let* ((params (get-lambda-simple-params exp))
                  (body (get-lambda-simple-body exp))
                  (bvars* (cons pvars bvars))
                  (pvars* params)
                  (all-but-last (get-all-but-last exp)))
             (append all-but-last (list (pe->lex-pe* body pvars* bvars*)))))
          ((is-opt-lambda? exp)
           (let* ((params (get-lambda-opt-params exp))
                  (body (get-lambda-opt-body exp))
                  (bvars* (cons pvars bvars))
                  (pvars* params)
                  (all-but-last (get-all-but-last exp)))
             (append all-but-last (list (pe->lex-pe* body pvars* bvars*)))))
          ((is-var-lambda? exp)
           (let* ((params (get-lambda-var-params exp))
                  (body (get-lambda-var-body exp))
                  (bvars* (cons pvars bvars))
                  (pvars* params)
                  (all-but-last (get-all-but-last exp)))
             (append all-but-last (list (pe->lex-pe* body pvars* bvars*)))))
          ((eq? (car exp) 'var) (var->lex-var (cadr exp) pvars bvars))
          (else (cons (pe->lex-pe* (car exp) pvars bvars) (pe->lex-pe* (cdr exp) pvars bvars))))))


(define pe->lex-pe
  (lambda (exp)
    (pe->lex-pe* exp '() '())))

(define is-lambda?
  (lambda (expr)
    (let ((tag (get-tag expr)))
      (or (eq? tag 'lambda-simple) (eq? tag 'lambda-opt) (eq? tag 'lambda-variadic)))))

(define atp
  (lambda (expr tp?)
    (let ((tag (get-tag expr)))
      (cond ((eq? tag 'const) expr)
            ((eq? tag 'fvar) expr)
            ((eq? tag 'pvar) expr)
            ((eq? tag 'bvar) expr)
            ((eq? tag 'var) expr)
            ((eq? tag 'or)
             (let ((all-but-last (get-all-but-last (cadr expr)))
                   (last (get-last (cadr expr))))
               `(or ,(append (map (lambda (x) (atp x #f)) all-but-last) (list (atp last tp?))))))
            ((eq? tag 'if3)
             (let ((test (cadr expr))
                   (dit (caddr expr))
                   (dif (cadddr expr)))
               `(if3 ,(atp test #f) ,(atp dit tp?) ,(atp dif tp?))))
            ((eq? tag 'define)
             (let ((var (cadr expr))
                   (peExpr (caddr expr)))
               `(define ,var ,(atp peExpr #f))))
            ((eq? tag 'seq)
             (let ((all-but-last (get-all-but-last (cadr expr)))
                   (last (get-last (cadr expr))))
               `(seq ,(append (map (lambda (x) (atp x #f)) all-but-last) (list (atp last tp?))))))
            ((is-lambda? expr)
             (let ((body (get-last expr))
                   (all-but-body (get-all-but-last expr)))
               `(,@all-but-body ,(atp body #t))))
            ((eq? tag 'applic)
             (if (eq? tp? #f)
                 `(applic ,(atp (cadr expr) #f) ,(map (lambda (x) (atp x #f)) (caddr expr)))
                 `(tc-applic ,(atp (cadr expr) #f) ,(map (lambda (x) (atp x #f)) (caddr expr)))))))))

(define annotate-tc
  (lambda (expr)
    (atp expr #f)))

(define file->sexprs
  (lambda (filename)
    (let ((input (open-input-file filename)))
      (letrec ((run
                (lambda ()
                  (let ((e (read input)))
                    (if (eof-object? e)
                        (begin (close-input-port input)
                               '())
                        (cons e (run)))))))
        (run)))))

(define ^^label
  (lambda (name)
    (let ((n 0))
      (lambda ()
        (set! n (+ n 1))
        (string-append name
                       (number->string n))))))


(define nl (list->string (list #\newline)))

(define label-not-proc "Lnot_proc")
(define label-end-program "Lend")

(define label-cons-code "L_Prim_cons")
(define ^label-cont (^^label "L_cont_"))
(define prologue
  (let ((label-cont (^label-cont)))
    (string-append
     "#include <stdio.h>" nl
     "#include <stdlib.h>" nl
     "#define DO_SHOW 2" nl
     "#include \"arch/cisc.h\"" nl
     "#include \"arch/info.h\"" nl
     "" nl
     "int main()" nl
     "{" nl
     "  int i,j;" nl ;Declared here because otherwise there could be multiple declerations in a file
     "  START_MACHINE;" nl
     "  JUMP(CONTINUE);" nl
     "#include \"arch/char.lib\"" nl
     "#include \"arch/io.lib\"" nl
     "#include \"arch/math.lib\"" nl
     "#include \"arch/string.lib\"" nl
     "#include \"arch/system.lib\"" nl
     "#include \"arch/scheme.lib\"" nl
     nl
     label-not-proc":" nl
     "  JUMP("label-end-program");" nl
     "CONTINUE:" nl
     "  /* definitions of some basic scheme objects */" nl
     "  /* this might be replaced later when symbols are properly implemented */" nl
     nl
     "  /* allocating 1000 memory cells */" nl
     "  ADD(IND(0), 1000);" nl 
     nl
     "  /* Void object definition */" nl
     "  MOV(IND(1), T_VOID);" nl
     "  #define SOB_VOID 1" nl
     nl
     "  /* Null (empty list) definition */" nl
     "  MOV(IND(2), T_NIL);" nl 
     "  #define SOB_NIL 2" nl 
     nl
     "  /* #f definition */" nl
     "  MOV(IND(3), T_BOOL);" nl
     "  MOV(IND(4), 0);" nl
     "  #define SOB_FALSE 3" nl 
     nl
     "  /* #t definition */" nl
     "  MOV(IND(5), T_BOOL);" nl
     "  MOV(IND(6), 1);" nl
     "  #define SOB_TRUE 5" nl
     nl
     "  /* cons code and definition */" nl
     "  JUMP("label-cont"); //skipping over the actual (cons) execution, because we only want to define it" nl
     label-cons-code":" nl
     "  PUSH(FP);" nl
     "  MOV(FP,SP);"  nl
     "  PUSH(FPARG(3)); //The cdr" nl
     "  PUSH(FPARG(2)); //The car" nl
     "  CALL(MAKE_SOB_PAIR);" nl
     "  DROP(2);" nl
     "  POP(FP);" nl
     "  RETURN;" nl
     label-cont":" nl
     "  MOV(IND(10), T_CLOSURE); //type" nl
     "  MOV(IND(11), 308618859); //env (there is no env when calling cons, so this is just a random number [my id])" nl
     "  MOV(IND(12), LABEL("label-cons-code")); //code address" nl
     "  #define PRIM_CONS 10" nl
     "  /* end of cons code and definition */" nl
   )))

(define create_mem_prologue 
  (lambda (consts-dict)
    (let ((consts-str (create-consts-string consts-dict))
          (first-addr (caar consts-dict))
      (string-append
       "  /* initializing the memory with constants found in the program */" nl
       "  long* mem_init = {"consts-str"}; //The memory image of the constants" nl
       "  memcpy(ADDR("first-addr"), mem_init, sizeof(mem_init)); //Copying the array into memory" nl
       "  /* end of memory initialization */" nl
       )))))

(define epilogue
  (string-append
   "  /* Stopping the machine */" nl
   label-end-program":" nl
   "  STOP_MACHINE;" nl
   "  return 0;" nl
   "}" nl))

(define epilogue-sexpr
  (string-append
   "  /* printing the content of R0 */" nl
   "  PUSH(R0);" nl
   "  CALL(WRITE_SOB);" nl ;TODO: This assumes the value of *R0 is a Scheme Object. What if it's not? 
   "  CALL(NEWLINE);" nl
   "  /* done printing the content of R0 */" nl
   ))
   

(define pe-seq?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'seq))))

(define pe-const?
  (lambda (pe)
    (eq? (car pe) 'const)))

(define pe-or?
  (lambda (pe)
    (eq? (car pe) 'or)))
  
(define code-gen-seq
  (lambda (e env-size param-size)
    (with e
          (lambda (seq exprs)
            (apply string-append
                   (map (lambda (pe)
                          (code-gen pe env-size param-size))
                        exprs))))))

(define get-const-addr
  (lambda (c dict)
    (cadr (assoc c dict))))

(define code-gen-const
  (lambda (e const-dict)
    (with e
          (lambda (const c)
            (let ((addr (cadr (assoc c const-dict))))
              (cond
               (assoc c const-dict)
               ((eq? c #f) (string-append
                            "  /* #f */" nl
                            "  MOV(R0, SOB_FALSE);" nl
                            "  /* end of #f */" nl))
               ((eq? c #t) (string-append
                            "  /* #t */" nl
                            "  MOV(R0, SOB_TRUE);" nl
                            "  /* end of #t */" nl))
               ((eq? c *void-object*) (string-append
                                       "  /* #<void> */" nl
                                       "  MOV(R0, SOB_VOID);" nl
                                       "  /* end of #<void> */" nl))
               ((eq? c '()) (string-append
                             "  /* '() (empty list) */" nl
                             "  MOV(R0, SOB_NIL);" nl
                             "  /* end of '() */" nl))
               ))))))

(define ^label-orexit (^^label "Lor_exit"))

(define code-gen-or
  (lambda (pe env-size param-size)
    (with pe
          (lambda (or pes)
            (let* ((first-pes (get-all-but-last pes))
                  (last-pe (get-last pes))
                  (label-exit (^label-orexit))
                  (first-pes-code 
                   (apply string-append
                          (map (lambda (e)
                                 (string-append
                                  (code-gen e env-size param-size)
                                  "  CMP(R0, SOB_FALSE);" nl
                                  "  JUMP_NE(" label-exit ");" nl))
                               first-pes)))
                  (last-pe-code (code-gen last-pe env-size param-size)))
              (string-append
               "  /* or */" nl
               first-pes-code
               last-pe-code
               label-exit ":"
               "  /* end of or*/" 
               nl))))))
                  
(define pe-if3?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'if3))))
                               
(define ^label-if3else (^^label "Lif3else"))
(define ^label-if3exit (^^label "Lif3exit"))
(define code-gen-if3
  (lambda (e env-size param-size)
    (with e
          (lambda (if3 test do-if-true do-if-false)
            (let ((code-test (code-gen test env-size param-size))
                  (code-dit (code-gen do-if-true env-size param-size))
                  (code-dif (code-gen do-if-false env-size param-size))
                  (label-else (^label-if3else))
                  (label-exit (^label-if3exit)))
              (string-append
               "  /* if3 */"
               code-test nl ; when run, the result of the test will be in R0
               "  CMP(R0, SOB_FALSE);" nl
               "  JUMP_EQ(" label-else ");" nl
               code-dit nl
               "  JUMP(" label-exit ");" nl
               label-else ":" nl
               code-dif nl
               label-exit ":" nl
               "  /* end of if3 */"
               nl))))))

(define pe-lambda-simple?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'lambda-simple))))

(define ^label-lambda-code (^^label "Llambdacode"))
(define ^label-lambda-exit (^^label "Llambdaexit"))
(define ^label-loop (^^label "Lloop"))
(define ^label-end-loop (^^label "Lendloop"))
(define ^label-copy-param (^^label "Lcopyparam"))

(define ^code-gen-lambda
  (lambda (type)
    (lambda (e env-size param-size)
      (let ((params (cond
                     ((or (eq? type 'opt) (eq? type 'simple)) (cadr e))
                     ((eq? type 'variadic) '())))
            (body (get-last e))
            (new-env-size-str (number->string (+ env-size 1)))
            (param-size-str (number->string param-size))
            (label-code (^label-lambda-code))
            (label-exit (^label-lambda-exit))
            (label-loop1 (^label-loop))
            (label-endloop1 (^label-end-loop))
            (label-loop2 (^label-loop))
            (label-endloop2 (^label-end-loop))
            (label-copyparam (^label-copy-param)))
        (string-append
         "  /* lambda-simple */" nl
         "  /* allocating memory for new environment */" nl
         "  PUSH("new-env-size-str");" nl
         "  CALL(MALLOC);" nl
         "  MOV(R1,R0);" nl
         "  /* end of memory allocation. The result is in R1 */" nl
         "  CMP(FP,2);" nl
         "  JUMP_LE("label-copyparam");" nl
         "  MOV(R2,FPARG(0)); //pointer to previous env is in R2" nl
         "  /* Copying old env to new env location. R1 points to the new env, R2 to the old */" nl
         "  MOV(R3, 0); //loop counter" nl
         "  MOV(R4, 1); //index into new env" nl
         label-loop1":" nl
         "  CMP(R3, "(number->string env-size)"); //loop condition" nl
         "  JUMP_GE("label-endloop1");" nl
         "  MOV(INDD(R1,R4), INDD(R2,R3));" nl
         "  ADD(R3, 1);" nl
         "  ADD(R4, 1);" nl
         "  JUMP("label-loop1");" nl
         label-endloop1":" nl
         ;"  for (i=0, j=1; i < IMM("(number->string env-size)"); i++, j++)" nl
         ;"  {" nl;
         ;"    MOV(INDD(R1,j), INDD(R2,i));" nl
         ;"  }" nl
         "  /* done copying old env to new env location. Note that R1[0] is reserved for the environment expansion (not part of the old env) */" nl
         label-copyparam":" nl
         "  /* allocating memory for a new row in the new environment array (will be pointer from R0[0]) */" nl
         "  PUSH("param-size-str");" nl
         "  CALL(MALLOC);" nl
         "  MOV(R3, R0);" nl
         "  /* done allocating memory. The address is in R3 */" nl
         "  /* Copying old params to the new environment (they turn from pvars to bvars)*/" nl
         "  MOV(R5,0); //loop counter" nl
         label-loop2":" nl
         "  CMP(R5,"param-size-str"); //loop condition" nl
         "  JUMP_GE("label-endloop2");" nl
         ;  /* The following 3 lines: r3[i] = FPARG(2+i). Note that FPARG(2+i) holds the i-th argument to the surrounding lambda */" nl
         "  MOV(R4,2);" nl
         "  ADD(R4,R5);" nl
         "  MOV(INDD(R3,R5),FPARG(R4));" nl
         "  ADD(R5,1);" nl
         "  JUMP("label-loop2");" nl
         label-endloop2":" nl  
         ;"  for (i=0; i < IMM("param-size-str"); i++)" nl
         ;"  {" nl
         ;"    /* The following 3 lines: r3[i] = FPARG(2+i). Note that FPARG(2+i) holds the i-th argument to the surrounding lambda */" nl
         ;"    MOV(R4,IMM(2));" nl
         ;"    ADD(R4,IMM(i));" nl
         ;"    MOV(INDD(R3,i),FPARG(R4));" nl
         ;"  }" nl
         "  /* Done copying old params to new environment */" nl
         "  MOV(INDD(R1,0), R3); //R1[0] now points to the first row in the new expanded environment" nl
         nl
         "  /* Create the closure object */" nl
         "  PUSH(3);" nl
         "  CALL(MALLOC);" nl
         "  MOV(INDD(R0,0), T_CLOSURE); //Type of the object" nl
         "  MOV(INDD(R0,1), R1); //Pointer to the environment" nl
         "  MOV(INDD(R0,2), LABEL("label-code")); //Pointer to the body code of the procedure" nl
         "  /* Done creating the closure object */" nl
         "  DROP(3); /* Remove all the PUSH operations done for the closure creation. THIS LINE FIXED A MAJOR BUG */" nl  ;;THIS WAS A MAJOR BUG FIX THAT TOOK ME SEVERAL HOURS TO FIND
         "  JUMP("label-exit");" nl
         nl
         label-code":" nl
         "  PUSH(FP);" nl
         "  MOV(FP,SP);" nl
         (cond
          ((eq? type 'simple) "  /* stack-correction-code-for-lambda-simple")
          ((or (eq? type 'opt) (eq? type 'variadic))
           (let ((params-length-str (number->string (length params))))
             (string-append
              "  /* stack-correction code for lambda-opt/variadic */" nl
              "  MOV(R1,FPARG(1+FPARG(1)));" nl
              "  /* Creating a list of optional arguments */" nl
              "  for (i = FPARG(1); i>1+"params-length-str"; i--) {" nl
              "    PUSH(R1); //cdr" nl
              "    PUSH(FPARG(i)); //car" nl
              "    CALL(MAKE_SOB_PAIR);" nl
              "    MOV(R1, R0); //put the result in R0" nl
              "    DROP(2);" nl
              "  }" nl
              "  /* Finished creating the list of optional arguments */" nl
              "  MOV(STACK(SP-5-"params-length-str"),R1); //Puting the optional arguments list after all the non-optional params" nl
              "  /* end of stack-correction code for lambda-opt/variadic" nl
              )))
          (else "  /* error */"))
         nl
         "  /* code-gen of the lambda body */" nl
         (code-gen body (+ env-size 1) (length params));
         "  /* end of code-gen for lambda body */" nl
         "  POP(FP);" nl
         "  RETURN;" nl
         label-exit":" nl)))))


(define pe-pvar?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'pvar))))

(define pe-bvar?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'bvar))))

(define code-gen-pvar
  (lambda (e env-size param-size)
    (with e
          (lambda (pvar var minor)
            (let ((minor-in-stack-str (number->string (+ minor 2))))
              (string-append
               "  /* pvar */" nl
               "  MOV(R0, FPARG("minor-in-stack-str"));" nl
               "  /* end of pvar */" nl
               ))))))

(define code-gen-bvar
  (lambda (e env-size param-size)
    (with e
          (lambda (bvar var major minor)
            (string-append
             "  /* bvar */" nl
             "  MOV(R0, FPARG(0)); /* env */" nl
             "  MOV(R0, INDD(R0,"(number->string major)")); /* major */" nl
             "  MOV(R0, INDD(R0,"(number->string minor)")); /* value */" nl
             "  /* end of bvar */" nl
             )))))
           
            
(define pe-applic?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'applic))))

(define code-gen-applic
  (lambda (e env-size param-size)
    (with e
          (lambda (applic proc args)
            (let ((args-num-string (number->string (+ (length args) 1)))) ;1 is added because of the extra Magic argument
              (string-append
               "  /* applic */" nl
               "  PUSH(SOB_NIL); //Magic argument. Reserving a space for a potential empty list of optional arguments." nl
               (apply string-append (map
                                     (lambda (arg)
                                       (string-append
                                        (code-gen arg env-size param-size)
                                        "  PUSH(R0);" nl))
                                     (reverse args)))
               "  PUSH("args-num-string")" nl
               (code-gen proc env-size param-size)
               "  CMP(IND(R0), T_CLOSURE);" nl 
               "  JUMP_NE("label-not-proc");" nl
               "  PUSH(INDD(R0,1));" nl
               "  CALLA(INDD(R0,2));" nl
               "  MOV(R1, STARG(0));" nl
               "  ADD(R1, 2);" nl
               "  DROP(R1);" nl
               " /* end of applic */" nl
               ))))))

(define pe-tc-applic?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'tc-applic))))

(define code-gen-tc-applic
  (lambda (e env-size param-size)
    (with e
          (lambda (tc-applic proc args)
            (let ((args-num-string (number->string (+ (length args) 1))) ;Adding 1 because of the extra Magic argument
                  (frame-copy-steps (number->string (+ (length args) 3)))
                  (label-loop (^label-loop))
                  (label-endloop (^label-end-loop)))
              (string-append
               "  /* tc-applic */" nl
               "  /* Pushing arguments */" nl
               "  PUSH(SOB_NIL); //Magic argument. Reserving a space for a potential empty list of optional arguments." nl
               (apply string-append (map
                                     (lambda (arg)
                                       (string-append
                                        (code-gen arg env-size param-size)
                                        "  PUSH(R0);" nl
                                        ))
                                     (reverse args)))
               "  /* Done pushing arguments */" nl
               "  PUSH("args-num-string"); //Pushing the number of arguments" nl
               (code-gen proc env-size param-size)
               "  CMP(INDD(R0,0),T_CLOSURE); //Make sure we got a closure" nl
               "  JUMP_NE("label-not-proc");" nl
               "  PUSH(INDD(R0,1)); //Push the environment onto the stack" nl
               "  PUSH(FPARG(-1)); //Push the return address from current frame (the same return address!)" nl
               "  MOV(R2, FPARG(1)); //n" nl
               "  ADD(R2,"args-num-string");" nl
               "  ADD(R2,7);" nl
               "  MOV(R3,SP);" nl
               "  SUB(R3,R2);" nl
               "  MOV(FP,FPARG(-2)); //Restore old FP in preperation for JUMP" nl
               "  /* Loop to overwrite the old frame */" nl
               ;"  MOV(R2, 0); //loop counter" nl
               ;"  MOV(R3, "args-num-string");" nl
               ;"  ADD(R3, 1);" nl
               ;label-loop":" nl
               ;"  CMP(R2,"frame-copy-steps"); //loop condition" nl
               ;"  JUMP_GE("label-endloop");" nl
               ;"  MOV(STACK(R1), STARG(R3));" nl
               ;"  ADD(R2,1); //incrementing loop counter" nl 
               ;"  ADD(R1,1);" nl
               ;"  MOV(R3, "args-num-string");" nl
               ;"  ADD(R3, 1);" nl
               ;"  SUB(R3, R2);" nl
               ;"  JUMP("label-loop");" nl
               ;label-endloop":" nl
               "  MOV(R1,FP);"  nl
               "  /* End of loop to overwrite old frame */" nl
               "  for (i=0; i<"args-num-string"+3; i++)" nl
               "  {" nl
               "    MOV(STACK(R3), STARG("args-num-string"+1-i));" nl
               "    ADD(R3,1);" nl
               "  }" nl
               "  MOV(SP,R3);" nl
               "  JUMPA(INDD(R0,2));" nl
               ;"  CALLA(INDD(R0,2)); //Jump to procedure code" nl
               ))))))
               
               
(define pe-fvar?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'fvar))))

(define code-gen-fvar
  (lambda (pe env-size param-size)
    (with pe
          (lambda (fvar name)
            (cond
             ((eq? name 'cons)
              (string-append
               "  /* (fvar cons) */" nl
               "  MOV(R0, PRIM_CONS);" nl
               "  /* end of (fvar cons) */;" nl
               )))))))

(define pe-lambda-opt?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'lambda-opt))))

(define pe-lambda-variadic?
  (lambda (pe)
    (and (list? pe) (eq? (car pe) 'lambda-variadic))))

;(define code-gen-lambda-opt
;  (lambda (pe env-size param-size)
;    (with pe
;          (lambda (lambda-opt param rest body)
;            (

(define code-gen
  (lambda (pe env-size param-size)
    (let ((code-gen-lambda-simple (^code-gen-lambda 'simple))
          (code-gen-lambda-opt (^code-gen-lambda 'opt))
          (code-gen-lambda-variadic (^code-gen-lambda 'variadic)))
      (cond
       ((pe-pvar? pe) (code-gen-pvar pe env-size param-size)) 
       ((pe-bvar? pe) (code-gen-bvar pe env-size param-size)) 
       ((pe-seq? pe) (code-gen-seq pe env-size param-size))
       ((pe-const? pe) (code-gen-const pe))
       ((pe-or? pe) (code-gen-or pe env-size param-size))
       ((pe-if3? pe) (code-gen-if3 pe env-size param-size))
       ((pe-lambda-simple? pe) (code-gen-lambda-simple pe env-size param-size))
       ((pe-applic? pe) (code-gen-applic pe env-size param-size))
       ((pe-tc-applic? pe) (code-gen-tc-applic pe env-size param-size))
       ((pe-fvar? pe) (code-gen-fvar pe env-size param-size))
       ((pe-lambda-opt? pe) (code-gen-lambda-opt pe env-size param-size))
       ((pe-lambda-variadic? pe) (code-gen-lambda-variadic pe env-size param-size))
       (else (void)))))) ;TODO: This needs to be replaced with an error message

(define write-to-file
  (lambda (filename string)
    (let ((p (open-output-file filename '(replace))))
      (begin
        (display string p)
        (close-port p)))))

(define compile-test
  (lambda (source)
    (let* ((sexprs (file->sexprs source))
           (output-code 
            (apply string-append (map
                                  (lambda (x)
                                    (code-gen x 0 0))
                                  (map parse sexprs))))
           (complete-code (string-append prologue output-code epilogue)))
      (write-to-file "out.c" complete-code))))

(define parse-full
  (lambda (sexpr)
    (annotate-tc (pe->lex-pe (parse sexpr)))))

(define topo-srt-const
  (lambda (e)
    (cond
      ((or  (null? e) (boolean? e)) `(,e))
      ((or (number? e) (string? e) (void? e)) `(,e))
      ((pair? e)
       `(,@(topo-srt-const (car e)) ,@(foo (cdr e)) ,e))
       ((vector? e)
        `(,@(apply append
                      (map topo-srt-const
                           (vector->list e))) ,e))
       ((symbol? e)
        `(,@(topo-srt-const (symbol->string e)) ,e))
       ;(else `(,e))
       )))

(define dedup
  (lambda (l)
    (reverse (dedup-helper (reverse l)))))

(define dedup-helper
  (lambda (l)
      (cond
       ((null? l) '())
       ((member (car l) (cdr l))
        (dedup-helper (cdr l)))
       (else (cons (car l) (dedup-helper (cdr l))))))))

(define extract-consts
  (lambda (pe)
    (cond
     ((atom? pe) '())
     ((null? pe) '())
     ((pe-const? pe) (list pe))
     (else (append (extract-consts (car pe)) (extract-consts (cdr pe)))))))

(define process-consts 
  (lambda (const-list)
    (dedup (apply append (map (lambda (const)
                                (dedup (topo-srt-const (cadr const))))
                              const-list)))))

(define get-item
  (lambda (l col)
    (if (eq? col 1)
        (car l)
        (get-item (cdr l) (- col 1))))) 

(define assoc-i
  (lambda (key l col)
    (if (equal? (get-item (car l) col) key)
        (car l)
        (assoc-i key (cdr l) col))))

(define consts->dict
  (lambda (const-lst acc-lst addr)
    (cond
     ((null? const-lst) (reverse acc-lst))
     (else 
      (let ((curr (car const-lst)))
        (cond
         ((number? curr)
          (consts->dict (cdr const-lst)
                        (cons  `(,addr ,curr (\T_NUMBER ,curr)) acc-lst)
                        (+ addr 2)))
         ((string? curr)
          (let ((ascii-chars (map char->integer (string->list curr))))
            (consts->dict (cdr const-lst)
                         (cons `(,addr ,curr (\T_STRING ,(string-length curr) ,@ascii-chars)) acc-lst)
                         (+ addr (+ (string-length curr) 1)))))
         ((pair? curr)
          (let ((addr_car (car (assoc-i (car curr) acc-lst 2)))
                (addr_cdr (car (assoc-i (cdr curr) acc-lst 2))))
            (consts->dict (cdr const-lst)
                         (cons `(,addr ,curr (\T_PAIR ,addr_car ,addr_cdr)) acc-lst)
                         (+ addr 3))))
         (else (consts->dict (cdr const-lst) acc-lst addr)))
        )))))

(define comma-sep
  (lambda (list)
    (fold-left (lambda (e x) (string-append e ", " x))
               `,(car list)
               (cdr list))))

(define list->list-of-strings
  (lambda (l)
    (map (lambda (x)
           (cond ((symbol? x) (symbol->string x))
                 ((number? x) (number->string x))))
         l)))

(define dict->consts-string
  (lambda (dict)
    (comma-sep (list->list-of-strings (apply append (map caddr dict))))))

(define create-consts-dict
  (lambda (pes addr)
    (let ((basic-consts2 `((,addr () (\T_NIL))
                           (,(+ addr 1) ,*void-object* (\T_VOID))
                           (,(+ addr 2) ,#f (\T_BOOL 0))
                           (,(+ addr 4) ,#t (\T_BOOL 1)))))
      (consts->dict (process-consts (extract-consts pes)) (reverse basic-consts2) (+ addr 6)))))
    
(define create-consts-string
  (lambda (dict)
      (dict->consts-string dict)))

(define compile-scheme-file
  (lambda (source target)
    (let* ((sexprs (file->sexprs source))
           (pe-lst (map (lambda (expr)
                          (parse-full expr))
                        sexprs))
           (const-dict (create-const-dict pe-lst 100))
           (mem-init (create-mem-prologue const-dict))
           (output-code 
            (apply string-append (map
                                  (lambda (x)
                                    (string-append
                                     (code-gen x 0 0)
                                     epilogue-sexpr))
                                  pe-lst)))
           (complete-code (string-append prologue mem-init output-code epilogue)))
      (write-to-file target complete-code))))

(define create-abc-dict
  (lambda (addr remaining)
    (if (>= remaining 0)
        (cons `(,(integer->char remaining) ,(+ addr remaining) (\T_CHAR ,remaining)) (create-abc-dict addr (- remaining 1)))
        '())))

(define abc-dict (create-abc-dict 10 255))
(parse-full '(begin 1 2 3 4 5))
(define pes (map parse-full '((begin '(1 2 3 4 "abc")) (begin "abc"))))
(define dict2 (create-consts-dict (map parse-full '((begin '(1 2 3 4 "abc")) (begin "abc"))) 100))
(create-consts-string dict2) 

(define d3 (create-consts-dict (map parse-full '((begin '(1 3 4 "abc")) (begin "abc") (begin '(1 23 "ad" "abc" 2 3)))) 100))
(create-consts-dict (map parse-full '((begin '(1 2 3 4 5)))) 100)
(define d2 (create-consts-dict (map parse-full '((begin 1 '()))) 100))
(define d1 (process-consts (extract-consts (parse-full '(begin '(1))))))
(process-consts (extract-consts (parse-full '(begin 1))))
dict2
(assoc-i 104 dict2 2)
(process-consts (extract-consts (map parse-full '((begin '(1 #f 2 3 4 "abc")) (begin "abc") (begin '(1 23 "ad" "abc" 2 3))))))
(create-consts-string d3)
