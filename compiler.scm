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
(define label-bin-plus-code "L_Prim_bin_plus")
(define label-bin-minus-code "L_Prim_bin_minus")
(define label-bin-mult-code "L_Prim_bin_mult")
(define label-bin-div-code "L_Prim_bin_div")
(define label-bin-less-code "L_Prim_bin_less")
(define label-bin-less-done "L_Prim_bin_less_done")
(define label-bin-eq-code "L_Prim_bin_eq")
(define label-bin-eq-done "L_Prim_bin_eq_done")
(define label-car-code "L_Prim_car_code")
(define label-cdr-code "L_Prim_cdr_code")
(define label-null?-code "L_Prim_null_code")
(define label-null?-done "L_Prim_null_done")
(define label-pair?-code "L_Prim_pair_code")
(define label-pair?-done "L_Prim_pair_done")
(define label-integer?-code "L_Prim_integer_code")
(define label-integer?-done "L_Prim_integer_done")
(define label-procedure?-code "L_Prim_procedure_code")
(define label-procedure?-done "L_Prim_procedure_done")
(define label-boolean?-code "L_Prim_boolean_code")
(define label-boolean?-done "L_Prim_boolean_done")
(define label-set-car-code "L_Prim_set_car_code")
(define label-set-cdr-code "L_Prim_set_cdr_code")
(define label-symbol-to-string-code "L_Prim_symbol_to_string_code")
(define label-str-to-sym-code "L_Prim_str_to_sym_code")
(define label-str-to-sym-loop "L_Prim_str_to_sym_loop")
(define label-str-to-sym-done "L_Prim_str_to_sym_done")
(define label-str-to-sym-new-sym "L_Prim_str_to_sym_new_sym")
(define label-string-ref-code "L_Prim_string_ref_code")
(define label-string-length-code "L_Prim_string_length_code")
(define label-char?-code "L_Prim_char_code")
(define label-char?-done "L_Prim_char_done")
(define label-string?-code "L_Prim_string_code")
(define label-string?-done "L_Prim_string_done")
(define label-symbol?-code "L_Prim_symbol_code")
(define label-symbol?-done "L_Prim_symbol_done")
(define label-char->integer-code "L_Prim_char_to_integer_code")
(define label-vector?-code "L_Prim_vector_code")
(define label-vector?-done "L_Prim_vector_done")
(define label-vector-length-code "L_Prim_vector_length_code")
(define label-vector-ref-code "L_Prim_vector_ref_code")
(define label-integer->char-code "L_Prim_integer_to_char_code")
(define label-make-string-code "L_Prim_make_string_code")
(define label-make-string-loop "L_Prim_make_string_loop")
(define label-make-string-done "L_Prim_make_string_done")
(define label-make-vector-create-val "L_Prim_make_vector_create_val")
(define label-make-vector-code "L_Prim_make_vector_code")
(define label-make-vector-loop "L_Prim_make_vector_loop")
(define label-make-vector-done "L_Prim_make_vector_done")
(define label-string-set!-code "L_Prim_string_string_set_code")
(define label-vector-set!-code "L_Prim_vector_vector_set_code")
(define ^label-cont (^^label "L_cont_"))

(define create-prologue
  (lambda (fvar-table first-sym-addr)
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
       ;"  /* allocating 1000 memory cells */" nl
       ;"  ADD(IND(0), 1000);" nl 
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
       "  /* Magic symbol devinition */" nl
       "  MOV(IND(7), T_SYMBOL);" nl
       "  MOV(IND(8), -1);" nl
       "  MOV(IND(9),"(number->string first-sym-addr)");" nl
       "  #define MAGIC_SYMBOL 7" nl
       nl
       "  /* cons code */" nl
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
       "  /* end of cons code */" nl
       nl
       "  /* bin+ code */" nl
       label-bin-plus-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  ADD(R1, IMM(R2));" nl
       "  PUSH(IMM(R1));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin+ code */" nl
       nl 
       "  /* bin- code */" nl
       label-bin-minus-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  SUB(R1, IMM(R2));" nl
       "  PUSH(IMM(R1));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin- code */" nl
       nl 
       "  /* bin* code */" nl
       label-bin-mult-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  MUL(R1, IMM(R2));" nl
       "  PUSH(IMM(R1));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin* code */" nl
       nl 
       "  /* bin/ code */" nl
       label-bin-div-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  DIV(R1, IMM(R2));" nl
       "  PUSH(IMM(R1));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin/ code */" nl
       nl 
       "  /* bin< code */" nl
       label-bin-less-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(IMM(R1),IMM(R2));" nl
       "  JUMP_GE("label-bin-less-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-bin-less-done":" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin< code */" nl
       nl 
       "  /* bin= code */" nl
       label-bin-eq-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1); //saving R1" nl
       "  PUSH(R2); //saving R2" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R1, INDD(R1,1));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(IMM(R1),IMM(R2));" nl
       "  JUMP_NE("label-bin-eq-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-bin-eq-done":" nl
       "  POP(R2); //restoring R2" nl
       "  POP(R1); //restoring R1" nl
       "  POP(FP); //restoring FP" nl
       "  RETURN;" nl
       "  /* end of bin= code */" nl
       nl 
       "  /* car code */" nl
       label-car-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R0, INDD(R1,1));" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of car code */" nl
       nl
       "  /* cdr code */" nl
       label-cdr-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R0, INDD(R1,2));" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of cdr code */" nl
       nl
       "  /* null? code */" nl
       label-null?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_NIL);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-null?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-null?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of null? code */" nl
       nl
       "  /* pair? code */" nl
       label-pair?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_PAIR);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-pair?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-pair?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of pair? code */" nl
       nl
       "  /* integer? code */" nl
       label-integer?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_INTEGER);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-integer?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-integer?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of integer? code */" nl
       nl
       "  /* procedure? code */" nl
       label-procedure?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_CLOSURE);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-procedure?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-procedure?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of procedure? code */" nl
       nl
       "  /* boolean? code */" nl
       label-boolean?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_BOOL);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-boolean?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-boolean?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of boolean? code */" nl
       nl
       "  /* set-car! code */" nl
       label-set-car-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(INDD(IMM(R1),1), R2);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  MOV(R0,SOB_VOID);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of set-car! code */" nl
       nl
       "  /* set-cdr! code */" nl
       label-set-cdr-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(INDD(IMM(R1),2), R2);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  MOV(R0,SOB_VOID);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of set-cdr! code */" nl
       nl
       "  /* symbol->string code  */" nl
       label-symbol-to-string-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R0,INDD(R1,1));" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of symbol->string code */" nl 
       nl
       "  /* string->symbol code  */" nl
       label-str-to-sym-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  PUSH(R4);" nl
       "  MOV(R4, MAGIC_SYMBOL); //R4 now points to the magic symbol" nl
       "  MOV(R1, INDD(R4,2)); //R1 now points to the first real symbol" nl
       "  MOV(R2, FPARG(2)); //R2 now holds the address of the parameter string" nl
       label-str-to-sym-loop":" nl
       "  CMP(R1,IMM(-1)); //Check if we are not at the last symbol" nl
       "  JUMP_EQ("label-str-to-sym-new-sym"); //If we are - there are no more symbols in the list, so create a new symbol." nl
       "  MOV(R3,INDD(R1,1)); //If the symbol exists - point R3 to its string" nl
       "  MOV(R0,R1); //And point R0 to the symbol itself (in preperation for returning)" nl
       "  CMP(R3,R2); //compare the string addresses of the current symbol and the parameter" nl
       "  JUMP_EQ("label-str-to-sym-done"); //If they are the same - we have found what we were looking for, so finish" nl
       "  MOV(R4, R1); //Otherwise, save the current symbol address in R4" nl
       "  MOV(R1, INDD(R1,2)); //and move R1 to the next symbol" nl
       "  JUMP("label-str-to-sym-loop");" nl
       label-str-to-sym-new-sym":" nl
       "  PUSH(IMM(3)); //Prepare to allocate memory for a new symbol" nl
       "  CALL(MALLOC); //Allocating memory, the address is in R0" nl
       "  DROP(1);" nl
       "  MOV(INDD(R4,2),IMM(R0)); //Update the pointer of the previous symbol to point to the new symbol" nl
       "  MOV(IND(R0), T_SYMBOL) //type" nl
       "  MOV(INDD(R0,1), IMM(R2)); //pointer to the string" nl
       "  MOV(INDD(R0,2), IMM(-1)); //pointer to the \"next\" symbol - but there is no next symbol, so it's -1" nl
       label-str-to-sym-done":" nl
       "  POP(R4)" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of string->symbol code */" nl 
       nl
       "  /* string-ref code */" nl
       label-string-ref-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  ADD(R2,2); //because we need to skip the first cell (number of chars), and the given index starts at 0" nl
       "  MOV(R3,INDD(R1,R2));" nl
       "  PUSH(R3);" nl
       "  CALL(MAKE_SOB_CHAR);" nl
       "  DROP(1);" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end-of string-ref code */" nl
       nl
       "  /* string-length code */" nl
       label-string-length-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, INDD(R1,1));" nl
       "  PUSH(R2);" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of string-length code */" nl
       nl
       "  /* char? code */" nl
       label-char?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1, FPARG(2));" nl
       "  PUSH(R1);" nl
       "  CALL(IS_SOB_CHAR);" nl
       "  DROP(1);" nl
       "  MOV(R1, IMM(R0));" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  CMP(R1, IMM(1));" nl
       "  JUMP_NE("label-char?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-char?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of char? code */" nl
       nl
       "  /* string? code */" nl
       label-string?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  MOV(R1, FPARG(2));" nl
       "  CMP(IND(R1), T_STRING);" nl
       "  JUMP_NE("label-string?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-string?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of string? code */" nl
       nl
       "  /* symbol? code */" nl
       label-symbol?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  MOV(R1, FPARG(2));" nl
       "  CMP(IND(R1), T_SYMBOL);" nl
       "  JUMP_NE("label-symbol?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-symbol?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of symbol? code */" nl
       nl
       "  /* char->integer code */" nl
       label-char->integer-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1,FPARG(2));" nl
       "  PUSH(INDD(R1,1));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(1);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of char->integer code */" nl
       nl 
       "  /* vector? code */" nl
       label-vector?-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R0, SOB_FALSE);" nl
       "  MOV(R1, FPARG(2));" nl
       "  CMP(IND(R1), T_VECTOR);" nl
       "  JUMP_NE("label-vector?-done");" nl
       "  MOV(R0, SOB_TRUE);" nl
       label-vector?-done":" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of vector? code */" nl
       nl
       "  /* vector-length code */" nl
       label-vector-length-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, INDD(R1,1));" nl
       "  PUSH(R2);" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(IMM(1));" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of vector-length code */" nl
       nl
       "  /* vector-ref code */" nl
       label-vector-ref-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  MOV(R1, FPARG(2));" nl
       "  MOV(R2, FPARG(3));" nl
       "  MOV(R2, INDD(R2,1));" nl
       "  ADD(R2,2); //because we need to skip the first cell (number of values), and the given index starts at 0" nl
       "  MOV(R0,INDD(R1,R2));" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end-of vector-ref code */" nl
       nl
       "  /* integer->char code */" nl
       label-integer->char-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  MOV(R1,FPARG(2));" nl
       "  PUSH(INDD(R1,1));" nl
       "  CALL(MAKE_SOB_CHAR);" nl
       "  DROP(1);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of integer->char code */" nl
       nl 
       "  /* make-string code */" nl
       label-make-string-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  PUSH(R4);" nl
       "  PUSH(R5);" nl
       "  MOV(R1,FPARG(1));" nl
       "  SUB(R1,1); //disregarding the magic argument" nl
       "  MOV(R2,FPARG(2));" nl
       "  MOV(R5, INDD(R2,1)); //placing the actual number in R2" nl
       "  MOV(R2,R5);" nl
       "  MOV(R4, IMM(112)); //Put in R4 the ascii of p, in preperation for the creation of the string" nl
       "  CMP(R1, IMM(1)); //Check if we got 1 or 2 arguments" nl
       "  JUMP_EQ("label-make-string-loop"); //if 1, go to the string-creation stage" nl
       "  MOV(R3, FPARG(3)); //Else, put in R3 the given character" nl
       "  MOV(R4, INDD(R3,1)); //Place in R4 the ascii code of the character in R3" nl
       label-make-string-loop":" nl
       "  CMP(R2,0);" nl
       "  JUMP_EQ("label-make-string-done");" nl
       "  PUSH(IMM(R4)); //Push the ascii code of the character to the stack, in preperation for MAKE_SOB_STRING" nl
       "  DECR(R2);" nl
       "  JUMP("label-make-string-loop");" nl
       label-make-string-done":" nl
       "  PUSH(IMM(R5)); //Push the number of characters" nl
       "  CALL(MAKE_SOB_STRING);" nl
       "  ADD(R5,1);" nl
       "  DROP(R5);" nl
       "  POP(R5);" nl
       "  POP(R4);" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of make-string code */" nl
       nl
       "  /* make-vector code */" nl
       label-make-vector-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  PUSH(R5);" nl
       "  MOV(R1,FPARG(1));" nl
       "  SUB(R1,1); //disregarding the magic argument" nl
       "  MOV(R2,FPARG(2));" nl
       "  MOV(R5, INDD(R2,1)); //placing the actual number in R5" nl
       "  MOV(R2,R5);" nl
       "  CMP(R1, IMM(1)); //Check if we got 1 or 2 arguments" nl
       "  JUMP_EQ("label-make-vector-create-val"); //if 1, go to the vector-creation stage" nl
       "  MOV(R3, FPARG(3)); " nl
       "  MOV(R0, INDD(R3,1)); " nl
       "  JUMP("label-make-vector-loop");" nl
       label-make-vector-create-val":" nl
       "  PUSH(IMM(7));" nl
       "  CALL(MAKE_SOB_INTEGER);" nl
       "  DROP(1);" nl
       label-make-vector-loop":" nl
       "  CMP(R2,0);" nl
       "  JUMP_EQ("label-make-vector-done");" nl
       "  PUSH(IMM(R0)); " nl
       "  DECR(R2);" nl
       "  JUMP("label-make-vector-loop");" nl
       label-make-vector-done":" nl
       "  PUSH(IMM(R5)); //Push the number of values" nl
       "  CALL(MAKE_SOB_VECTOR);" nl
       "  ADD(R5,1);" nl
       "  DROP(R5);" nl
       "  POP(R5);" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of make-vector code */" nl
       nl
       "  /* string-set! code */" nl
       label-string-set!-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  PUSH(R4);" nl
       "  MOV(R1, FPARG(2)); //put in R1 the pointer to the string we want to set!" nl
       "  MOV(R4, FPARG(3)); //put in R4 the pointer to the character index we want to set!" nl
       "  MOV(R2, INDD(R4,IMM(1))); //put in R2 the actual character index" nl;
       "  MOV(R4, FPARG(4)); //put in R4 the character we want to put in the string" nl
       "  MOV(R3, INDD(R4,1)); //put in R3 the ascii number of the character we want to put" nl
       "  ADD(R2, IMM(2)); //increment the index by 2 (skip first cell and take into account that the index starts from 0)" nl
       "  MOV(INDD(R1,R2),IMM(R3)); //change the string" nl
       "  MOV(R0,SOB_VOID); //we want to return void?" nl
       "  POP(R4);" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of string-set! code */" nl
       nl
       "  /* vector-set! code */" nl
       label-vector-set!-code":" nl
       "  PUSH(FP);" nl
       "  MOV(FP,SP);" nl
       "  PUSH(R1);" nl
       "  PUSH(R2);" nl
       "  PUSH(R3);" nl
       "  MOV(R1, FPARG(2)); //put in R1 the pointer to the vector we want to set!" nl
       "  MOV(R3, FPARG(3)); //put in R3 the pointer to the index we want to set!" nl
       "  MOV(R2, INDD(R3,IMM(1))); //put in R2 the actual index" nl;
       "  MOV(R3, FPARG(4)); //put in R3 the object we want to put in the vector" nl
       "  ADD(R2, IMM(2)); //increment the index by 2 (skip first cell and take into account that the index starts from 0)" nl
       "  MOV(INDD(R1,R2),IMM(R3)); //change the vector" nl
       "  MOV(R0,SOB_VOID); //we want to return void?" nl
       "  POP(R3);" nl
       "  POP(R2);" nl
       "  POP(R1);" nl
       "  POP(FP);" nl
       "  RETURN;" nl
       "  /* end of vector-set! code */" nl
       nl


       label-cont":" nl
       "  NOP;" nl
       (gen-closure-def 'cons label-cons-code fvar-table)
       (gen-closure-def 'bin+ label-bin-plus-code fvar-table)
       (gen-closure-def 'bin- label-bin-minus-code fvar-table)
       (gen-closure-def 'bin* label-bin-mult-code fvar-table)
       (gen-closure-def 'bin/ label-bin-div-code fvar-table)
       (gen-closure-def 'bin< label-bin-less-code fvar-table)
       (gen-closure-def 'bin= label-bin-eq-code fvar-table)
       (gen-closure-def 'car label-car-code fvar-table)
       (gen-closure-def 'cdr label-cdr-code fvar-table)
       (gen-closure-def 'null? label-null?-code fvar-table)
       (gen-closure-def 'pair? label-pair?-code fvar-table)
       (gen-closure-def 'integer? label-integer?-code fvar-table)
       (gen-closure-def 'procedure? label-procedure?-code fvar-table)
       (gen-closure-def 'boolean? label-boolean?-code fvar-table)
       (gen-closure-def 'set-car! label-set-car-code fvar-table)
       (gen-closure-def 'set-cdr! label-set-cdr-code fvar-table)
       (gen-closure-def 'symbol->string label-symbol-to-string-code fvar-table)
       (gen-closure-def 'string->symbol label-str-to-sym-code fvar-table)
       (gen-closure-def 'string-ref label-string-ref-code fvar-table)
       (gen-closure-def 'string-length label-string-length-code fvar-table)
       (gen-closure-def 'char? label-char?-code fvar-table)
       (gen-closure-def 'string? label-string?-code fvar-table)
       (gen-closure-def 'symbol? label-symbol?-code fvar-table)
       (gen-closure-def 'char->integer label-char->integer-code fvar-table)
       (gen-closure-def 'vector? label-vector?-code fvar-table)
       (gen-closure-def 'vector-length label-vector-length-code fvar-table)
       (gen-closure-def 'vector-ref label-vector-ref-code fvar-table)
       (gen-closure-def 'integer->char label-integer->char-code fvar-table)
       (gen-closure-def 'make-string label-make-string-code fvar-table)
       (gen-closure-def 'make-vector label-make-vector-code fvar-table)
       (gen-closure-def 'string-set! label-string-set!-code fvar-table)
       (gen-closure-def 'vector-set! label-vector-set!-code fvar-table)
       ))))

(define place-prim-ptr
  (lambda (prim-name prim-addr fvar-table)
    (let ((fvar-addr-str (number->string (car (assoc-i prim-name fvar-table 2)))))
      (string-append
       "  MOV(IND("fvar-addr-str"),IMM("(number->string prim-addr)"));" nl
       ))))

(define gen-closure-def
  (lambda (prim-name code-label fvar-table)
    (cond ((null? fvar-table) (string-append))
          ((eq? (assoc-i prim-name fvar-table 2) #f) "")
          (else 
           (let ((addr (get-next-addr))
                 (env-str "308618859"))
             (string-append
              "  /* "(symbol->string prim-name)" closure definition */" nl
              "  MOV(IND("(number->string addr)"), T_CLOSURE); //type" nl
              "  MOV(IND("(number->string (+ addr 1))"), "env-str"); //env" nl
              "  MOV(IND("(number->string (+ addr 2))"), LABEL("code-label")); //code-address" nl
              (place-prim-ptr prim-name addr fvar-table)
              "  /* end of "(symbol->string prim-name)" closure definition */" nl
              nl
              ))))))

(define ^next+3
  (lambda (first)
    (let ((n first))
      (lambda ()
        (set! n (+ n 3))
        n))))

(define get-next-addr (^next+3 50))

(define create-mem-prologue 
  (lambda (consts-dict fvar-dict)
    (let* ((consts-str (create-consts-string consts-dict))
           (num-of-consts (get-consts-size consts-dict))
           (num-of-fvars (get-fvar-size fvar-dict))
           (first-addr (caar consts-dict))
           (last-addr (+ first-addr num-of-consts num-of-fvars 1)))
      (string-append
       "  /* initializing the memory with constants found in the program */" nl
       "  long mem_init["(number->string num-of-consts)"] = {"consts-str"}; //The memory image of the constants" nl
       "  memcpy(&ADDR("(number->string first-addr)"), mem_init, sizeof(mem_init)); //Copying the array into memory" nl
       "  MOV(IND(0),"(number->string last-addr)"); //reserving space for fvars" nl
       "  /* end of memory initialization */" nl
       ))))

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
   "  DROP(1);" nl
   "  /* done printing the content of R0 */" nl
   ))
   
(define code-gen-seq
  (lambda (e env-size param-size const-table fvar-table)
    (with e
          (lambda (seq exprs)
            (apply string-append
                   (map (lambda (pe)
                          (code-gen pe env-size param-size const-table fvar-table))
                        exprs))))))

(define get-const-addr
  (lambda (c dict)
    (cadr (assoc c dict))))

(define code-gen-const
  (lambda (e env-size param-size const-dict fvar-table)
    (with e
          (lambda (const c)
            (let ((addr (number->string (car (assoc-i c const-dict 2)))))
              (string-append
               "  /* constant */" nl
               "  MOV(R0,"addr"); //The calculated address from the symbol table" nl
               "  /* end of constant */" nl
               ))))))
              ;(cond
              ; (assoc c const-dict)
              ; ((eq? c #f) (string-append
              ;              "  /* #f */" nl
              ;              "  MOV(R0, SOB_FALSE);" nl
              ;              "  /* end of #f */" nl))
              ; ((eq? c #t) (string-append
              ;              "  /* #t */" nl
              ;              "  MOV(R0, SOB_TRUE);" nl
              ;              "  /* end of #t */" nl))
              ; ((eq? c *void-object*) (string-append
              ;                         "  /* #<void> */" nl
              ;                         "  MOV(R0, SOB_VOID);" nl
              ;                         "  /* end of #<void> */" nl))
              ; ((eq? c '()) (string-append
              ;               "  /* '() (empty list) */" nl
              ;               "  MOV(R0, SOB_NIL);" nl
              ;               "  /* end of '() */" nl))
              ; ))))))

(define ^label-orexit (^^label "Lor_exit"))

(define code-gen-or
  (lambda (pe env-size param-size const-table fvar-table)
    (with pe
          (lambda (or pes)
            (let* ((first-pes (get-all-but-last pes))
                  (last-pe (get-last pes))
                  (label-exit (^label-orexit))
                  (SOB_FALSE (number->string (car (assoc-i #f const-table 2))))
                  (first-pes-code 
                   (apply string-append
                          (map (lambda (e)
                                 (string-append
                                  (code-gen e env-size param-size const-table fvar-table)
                                  "  CMP(R0,"SOB_FALSE");" nl
                                  "  JUMP_NE(" label-exit ");" nl))
                               first-pes)))
                  (last-pe-code (code-gen last-pe env-size param-size const-table fvar-table)))
              (string-append
               "  /* or */" nl
               first-pes-code
               last-pe-code
               label-exit ":"
               "  /* end of or*/" 
               nl))))))
                  
(define ^label-if3else (^^label "Lif3else"))
(define ^label-if3exit (^^label "Lif3exit"))
(define code-gen-if3
  (lambda (e env-size param-size const-table fvar-table)
    (with e
          (lambda (if3 test do-if-true do-if-false)
            (let ((code-test (code-gen test env-size param-size const-table fvar-table))
                  (code-dit (code-gen do-if-true env-size param-size const-table fvar-table))
                  (code-dif (code-gen do-if-false env-size param-size const-table fvar-table))
                  (SOB_FALSE (number->string (car (assoc-i #f const-table 2))))
                  (label-else (^label-if3else))
                  (label-exit (^label-if3exit)))
              (string-append
               "  /* if3 */"
               code-test nl ; when run, the result of the test will be in R0
               "  CMP(R0,"SOB_FALSE");" nl
               "  JUMP_EQ(" label-else ");" nl
               code-dit nl
               "  JUMP(" label-exit ");" nl
               label-else ":" nl
               code-dif nl
               label-exit ":" nl
               "  /* end of if3 */"
               nl))))))
(define ^label-lambda-code (^^label "Llambdacode"))
(define ^label-lambda-exit (^^label "Llambdaexit"))
(define ^label-loop (^^label "Lloop"))
(define ^label-end-loop (^^label "Lendloop"))
(define ^label-copy-param (^^label "Lcopyparam"))

(define ^code-gen-lambda
  (lambda (type)
    (lambda (e env-size param-size const-table fvar-table)
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
         (code-gen body (+ env-size 1) (length params) const-table fvar-table);
         "  /* end of code-gen for lambda body */" nl
         "  POP(FP);" nl
         "  RETURN;" nl
         label-exit":" nl)))))

(define code-gen-pvar
  (lambda (e env-size param-size const-table fvar-table)
    (with e
          (lambda (pvar var minor)
            (let ((minor-in-stack-str (number->string (+ minor 2))))
              (string-append
               "  /* pvar */" nl
               "  MOV(R0, FPARG("minor-in-stack-str"));" nl
               "  /* end of pvar */" nl
               ))))))

(define code-gen-bvar
  (lambda (e env-size param-size const-table fvar-table)
    (with e
          (lambda (bvar var major minor)
            (string-append
             "  /* bvar */" nl
             "  MOV(R0, FPARG(0)); /* env */" nl
             "  MOV(R0, INDD(R0,"(number->string major)")); /* major */" nl
             "  MOV(R0, INDD(R0,"(number->string minor)")); /* value */" nl
             "  /* end of bvar */" nl
             )))))
           
            
(define code-gen-applic
  (lambda (e env-size param-size const-table fvar-table)
    (with e
          (lambda (applic proc args)
            (let ((args-num-string (number->string (+ (length args) 1)))) ;1 is added because of the extra Magic argument
              (string-append
               "  /* applic */" nl
               "  PUSH(SOB_NIL); //Magic argument. Reserving a space for a potential empty list of optional arguments." nl
               (apply string-append (map
                                     (lambda (arg)
                                       (string-append
                                        (code-gen arg env-size param-size const-table fvar-table)
                                        "  PUSH(R0);" nl))
                                     (reverse args)))
               "  PUSH("args-num-string")" nl
               (code-gen proc env-size param-size const-table fvar-table)
               "  CMP(IND(R0), T_CLOSURE);" nl 
               "  JUMP_NE("label-not-proc");" nl
               "  PUSH(INDD(R0,1));" nl
               "  CALLA(INDD(R0,2));" nl
               "  MOV(R1, STARG(0));" nl
               "  ADD(R1, 2);" nl
               "  DROP(R1);" nl
               " /* end of applic */" nl
               ))))))

(define code-gen-tc-applic
  (lambda (e env-size param-size const-table fvar-table)
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
                                        (code-gen arg env-size param-size const-table fvar-table)
                                        "  PUSH(R0);" nl
                                        ))
                                     (reverse args)))
               "  /* Done pushing arguments */" nl
               "  PUSH("args-num-string"); //Pushing the number of arguments" nl
               (code-gen proc env-size param-size const-table fvar-table)
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
               
               
(define code-gen-define
  (lambda (pe env-size param-size const-table fvar-table)
    (with pe
          (lambda (def var value)
            (let ((fvar-addr (car (assoc-i (cadr var) fvar-table 2)))
                  (SOB_VOID (car (assoc-i *void-object* const-table 2))))
              (string-append
               "  /* code-gen for (define a e) */" nl
               "  /* evaluating the value of e */" nl
               (code-gen value env-size param-size const-table fvar-table)
               "  /* finished evaluating the value of e */" nl
               "  MOV(IND("(number->string fvar-addr)"),R0); //setting the fvar value in the memory" nl
               "  MOV(R0,"(number->string SOB_VOID)"); //define should return #<void>" nl 
               "  /* end of code-gen for (define a e) */" nl
               ))))))

(define fvar-code
  (lambda (prim-name-str label-name-str)
    (string-append
     "  /* (fvar "prim-name-str") */" nl
     "  MOV(R0, "label-name-str");" nl
     "  /* end of (fvar "prim-name-str") */" nl)))
      
(define code-gen-fvar
  (lambda (pe env-size param-size consts-table fvar-table)
    (with pe
          (lambda (fvar name)
            (let ((fvar-addr (car (assoc-i name fvar-table 2))))
              (if fvar-addr
                  (string-append
                   "  /* (fvar "(symbol->string name)") */" nl
                   "  MOV(R0,IND("(number->string fvar-addr)")); //returning the value of the fvar" nl
                   "  /* end of (fvar "(symbol->string name)") */" nl
                   )
                  (string-append
                   " /* AN ERROR OF SOME SORT!! TODO!!! */"
                   )))))))
                     
(define ^pe-??
  (lambda (tag)
    (lambda (pe)
      (and (list? pe) (eq? (car pe) tag)))))

(define pe-fvar? (^pe-?? 'fvar))
(define pe-pvar? (^pe-?? 'pvar))
(define pe-bvar? (^pe-?? 'bvar))
(define pe-seq? (^pe-?? 'seq))
(define pe-const? (^pe-?? 'const))
(define pe-or? (^pe-?? 'or))
(define pe-if3? (^pe-?? 'if3))
(define pe-lambda-simple? (^pe-?? 'lambda-simple))
(define pe-applic? (^pe-?? 'applic))
(define pe-tc-applic? (^pe-?? 'tc-applic))
(define pe-lambda-opt? (^pe-?? 'lambda-opt))
(define pe-lambda-variadic? (^pe-?? 'lambda-variadic))
(define pe-define? (^pe-?? 'define))

(define code-gen-lambda-simple (^code-gen-lambda 'simple))
(define code-gen-lambda-opt (^code-gen-lambda 'opt))
(define code-gen-lambda-variadic (^code-gen-lambda 'variadic))
(define code-gen
  (lambda (pe env-size param-size const-table fvar-table)
    (let ((params `(,pe ,env-size ,param-size ,const-table ,fvar-table)))
      (cond
       ((pe-pvar? pe) (apply code-gen-pvar params))
       ((pe-bvar? pe) (apply code-gen-bvar params))
       ((pe-seq? pe) (apply code-gen-seq params))
       ((pe-const? pe) (apply code-gen-const params))
       ((pe-or? pe) (apply code-gen-or params))
       ((pe-if3? pe) (apply code-gen-if3 params))
       ((pe-lambda-simple? pe) (apply code-gen-lambda-simple params))
       ((pe-applic? pe) (apply code-gen-applic params))
       ((pe-tc-applic? pe) (apply code-gen-tc-applic params))
       ((pe-lambda-opt? pe) (apply code-gen-lambda-opt params))
       ((pe-lambda-variadic? pe) (apply code-gen-lambda-variadic params))
       ((pe-define? pe) (apply code-gen-define params))
       ((pe-fvar? pe) (apply code-gen-fvar params))
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
      output-code)))

(define parse-full
  (lambda (sexpr)
    (annotate-tc (pe->lex-pe (parse sexpr)))))

(define topo-srt-const
  (lambda (e)
    (cond
      ((or  (null? e) (boolean? e)) `(,e))
      ((or (number? e) (string? e) (void? e)) `(,e))
      ((pair? e)
       `(,@(topo-srt-const (car e)) ,@(topo-srt-const (cdr e)) ,e))
       ((vector? e)
        `(,@(apply append
                      (map topo-srt-const
                           (vector->list e))) ,e))
       ((symbol? e)
        `(,@(topo-srt-const (symbol->string e)) ,e))
       ((char? e)
        `(,e))
       (else `(,e))
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
       (else (cons (car l) (dedup-helper (cdr l)))))))

(define ^extract-by-tag
  (lambda (tag)
    (letrec ((run
              (lambda (pe)
                (cond
                 ((atom? pe) '())
                 ((null? pe) '())
                 ((eq? (car pe) tag) (list pe))
                 (else (append (run (car pe)) (run (cdr pe))))))))
      run)))

(define extract-consts (^extract-by-tag 'const))
(define extract-fvars (^extract-by-tag 'fvar))

(define process-fvars
  (lambda (fvar-list)
    (dedup (apply append (map cdr fvar-list)))))

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
    (cond ((null? l) #f)
          ((equal? (get-item (car l) col) key) (car l))
          (else (assoc-i key (cdr l) col)))))

(define fvars->dict
  (lambda (fvar-lst acc-lst addr)
    (cond
     ((null? fvar-lst) (reverse acc-lst))
     (else
      (let ((curr (car fvar-lst)))
        (fvars->dict (cdr fvar-lst)
                     (cons `(,addr ,curr) acc-lst)
                     (+ addr 1)))))))

(define get-first-sym-addr
  (lambda (const-dict)
    (if (null? const-dict)
        -1
        (let ((type (get-item (get-item (car const-dict) 3) 1)))
          (if (eq? type '\T_SYMBOL)
              (caar const-dict)
              (get-first-sym-addr (cdr const-dict)))))))

(define consts->dict
  (lambda (const-lst acc-lst addr last-sym-addr)
    (cond
     ((null? const-lst) (reverse acc-lst))
     (else 
      (let ((curr (car const-lst)))
        (cond
         ((number? curr)
          (consts->dict (cdr const-lst)
                        (cons  `(,addr ,curr (\T_INTEGER ,curr)) acc-lst)
                        (+ addr 2)
                        last-sym-addr))
         ((string? curr)
          (let ((ascii-chars (map char->integer (string->list curr))))
            (consts->dict (cdr const-lst)
                          (cons `(,addr ,curr (\T_STRING ,(string-length curr) ,@ascii-chars)) acc-lst)
                          (+ addr (+ (string-length curr) 2))
                          last-sym-addr)))
         ((pair? curr)
          (let ((addr-car (car (assoc-i (car curr) acc-lst 2)))
                (addr-cdr (car (assoc-i (cdr curr) acc-lst 2))))
            (consts->dict (cdr const-lst)
                          (cons `(,addr ,curr (\T_PAIR ,addr-car ,addr-cdr)) acc-lst)
                          (+ addr 3)
                          last-sym-addr)))
         ((symbol? curr)
          (let ((addr-str (car (assoc-i (symbol->string curr) acc-lst 2))))
            (consts->dict (cdr const-lst)
                          (cons `(,addr ,curr (\T_SYMBOL ,addr-str ,last-sym-addr)) acc-lst)
                          (+ addr 3)
                          addr)))
         ((char? curr)
          (consts->dict (cdr const-lst)
                        (cons `(,addr ,curr (\T_CHAR ,(char->integer curr))) acc-lst)
                        (+ addr 2)
                        last-sym-addr))
         ((vector? curr)
          (let ((members (map
                          (lambda (mem)
                            (car (assoc-i mem acc-lst 2)))
                          (vector->list curr))))
            (consts->dict (cdr const-lst)
                          (cons `(,addr ,curr (\T_VECTOR ,(length members) ,@members)) acc-lst)
                          (+ addr 2 (length members))
                          last-sym-addr)))
         (else (consts->dict (cdr const-lst) acc-lst addr last-sym-addr)))
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

(define get-fvar-size
  (lambda (dict)
    (length dict)))

(define get-consts-size
  (lambda (dict)
    (length (list->list-of-strings (apply append (map caddr dict))))))

(define dict->consts-string
  (lambda (dict)
    (comma-sep (list->list-of-strings (apply append (map caddr dict))))))

(define create-consts-dict
  (lambda (pes addr)
    (let ((basic-consts2 `((,addr () (\T_NIL))
                           (,(+ addr 1) ,*void-object* (\T_VOID))
                           (,(+ addr 2) ,#f (\T_BOOL 0))
                           (,(+ addr 4) ,#t (\T_BOOL 1)))))
      (consts->dict (process-consts (extract-consts pes)) (reverse basic-consts2) (+ addr 6) -1))))
    
(define create-consts-string
  (lambda (dict)
      (dict->consts-string dict)))

(define create-fvar-dict
  (lambda (pes addr)
    (fvars->dict (process-fvars (extract-fvars pes)) '() addr)))

(define compile-scheme-file
  (lambda (source target)
    (let* ((sexprs (file->sexprs source))
           (pe-lst (map (lambda (expr)
                          (parse-full expr))
                        sexprs))
           (mem-init-addr 200)
           (const-dict (create-consts-dict pe-lst mem-init-addr))
           (consts-length (get-consts-size const-dict))
           (fvar-dict (create-fvar-dict pe-lst (+ mem-init-addr consts-length)))
           (mem-init (create-mem-prologue const-dict fvar-dict))
           (first-sym-addr (get-first-sym-addr const-dict))
           (prologue (create-prologue fvar-dict first-sym-addr))
           (output-code 
            (apply string-append (map
                                  (lambda (x)
                                    (string-append
                                     (code-gen x 0 0 const-dict fvar-dict)
                                     epilogue-sexpr))
                                  pe-lst)))
           (complete-code (string-append prologue mem-init output-code epilogue)))
      (write-to-file target complete-code))))

(define create-abc-dict
  (lambda (addr remaining)
    (if (>= remaining 0)
        (cons `(,(integer->char remaining) ,(+ addr remaining) (\T_CHAR ,remaining)) (create-abc-dict addr (- remaining 1)))
        '())))


;(define d3 (create-consts-dict (map parse-full '((begin '(1 3 4 "abc")) (begin "abc") (begin '(1 23 "ad" "abc" 2 3)))) 100))
;(create-consts-dict (map parse-full '((begin '(1 2 3 4 5)))) 100)
;(define d2 (create-consts-dict (map parse-full '((begin 1 '()))) 100))
;(define d1 (process-consts (extract-consts (parse-full '(begin '(1))))))
;(process-consts (extract-consts (parse-full '(begin 1))))
;dict2
;(assoc-i 104 dict2 2)
;(process-consts (extract-consts (map parse-full '((begin '(1 #f 2 3 4 "abc")) (begin "abc") (begin '(1 23 "ad" "abc" 2 3))))))
;(create-consts-string d3)
;(create-consts-string (create-consts-dict (map parse-full '(#f)) 100))
;(process-consts (extract-consts (map parse-full '(#f))))
;(parse-full '#f)

;(parse-full '(begin 'm))
(define t1 (process-consts (extract-consts (parse-full '(begin 'm)))))
t1
;(consts->dict t1 '() 100)
;(create-consts-dict t1 100) 
;(create-consts-dict (process-consts (extract-consts (parse-full '(begin 'm)))) 100)
;(define d1 (create-consts-dict (map parse-full '((begin 'm))) 100))
;(create-consts-string d1)
;(parse-full '(#(1 2 3)))
;(define f1 (process-fvars (extract-fvars (parse-full '(define fact (lambda (n) (if (zero? n) 1 (* n (fact (- n 1))))))))))
;(fvars->dict f1 '() 200)
;(fvars->dict (process-fvars (extract-fvars (map parse-full (file->sexprs "tests/define.scm")))) '() 200)
;(define c1 (process-consts (extract-consts (parse-full ''(a)))))
;c1
;(consts->dict c1 '() 100 -1)

(define d2 (create-consts-dict (map parse-full (file->sexprs "tests/symbols.scm")) 100))
d2
(get-first-sym-addr d2)
(extract-consts (parse-full '#\a))
(process-consts (extract-consts (parse-full '#\a)))
(define d3 (consts->dict (process-consts (extract-consts (parse-full '#\a))) '() 100 -1))
d2
d3
(define d4 (consts->dict (process-consts (extract-consts (parse-full ''#(a 2 #(1 2) 3)))) '() 100 -1))
(define d5 (create-consts-dict (map parse-full (file->sexprs "test-vec/vector.scm")) 100))

d4

d3

d5
