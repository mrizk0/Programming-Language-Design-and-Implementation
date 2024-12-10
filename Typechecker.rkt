#lang plaitypus

(define-type TLFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TLFAE) (r : TLFAE)]
  [sub (l : TLFAE) (r : TLFAE)]
  [eql (l : TLFAE) (r : TLFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TLFAE) (thn : TLFAE) (els : TLFAE)]
  [fun (arg : symbol) (typ : Type) (body : TLFAE)]
  [app (rator : TLFAE) (rand : TLFAE)]
  [consl (fst : TLFAE) (rst : TLFAE)]
  [firstl (lst : TLFAE)]
  [restl (lst : TLFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TLFAE)]
  [makevector (size : TLFAE) (initial : TLFAE)]
  [set (vec : TLFAE) (index : TLFAE) (val : TLFAE)]
  [lengthl (col : TLFAE)]
  [get (col : TLFAE) (index : TLFAE)])

(define-type Type
  [numberT]
  [booleanT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)]
  [vectorT (typ : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

(define typecheck : (TLFAE TypeEnv -> Type)
  (lambda (a-tlfae gamma)
    (type-case TLFAE a-tlfae
      [num (n)
           (numberT)]
      [bool (b)
            (booleanT)]
      [add (l r)
           (unless (numberT? (typecheck l gamma))
             (error 'typecheck "expected number"))
           (unless (numberT? (typecheck r gamma))
             (error 'typecheck "expected number"))
           (numberT)]
      [sub (l r)
           (unless (numberT? (typecheck l gamma))
             (error 'typecheck "expected number"))
           (unless (numberT? (typecheck r gamma))
             (error 'typecheck "expected number"))
           (numberT)]
      [eql (l r)
           (unless (numberT? (typecheck l gamma))
             (error 'typecheck "expected number"))
           (unless (numberT? (typecheck r gamma))
             (error 'typecheck "expected number"))
           (booleanT)]
      [id (name)
          (lookup-type name gamma)]
      [ifthenelse (tst thn els)
                  (unless (booleanT? (typecheck tst gamma))
                    (error 'typecheck "expected boolean"))
                  (unless (equal? (typecheck thn gamma)
                                  (typecheck els gamma))
                    (error 'typecheck "type mismatch"))
                  (typecheck thn gamma)]
      [fun (arg typ body)
           (define tau1 typ)
           (define tau2 (typecheck body (aBind arg
                                               typ
                                               gamma)))
           (arrowT tau1 tau2)]
      [app (rator rand)
           (define fun-type (typecheck rator gamma))
           (type-case Type fun-type
             [arrowT (tau2 tau3)
                     (define arg-type (typecheck rand gamma))
                     (unless (equal? arg-type tau2)
                       (error 'typecheck "type mismatch"))
                     tau3]
             [else (error 'typecheck "expected function")])]
      [consl (fst rst)
             (unless (listT? (typecheck rst gamma))
               (error 'typecheck "expected list"))
             (type-case Type (typecheck rst gamma)
               [listT (x)
                      (if (equal? x (typecheck fst gamma))
                          (listT x)
                          (error 'typecheck "type mismatch"))]
               [else (error 'typecheck "expected list")])]
      [firstl (lst)
              (unless (listT? (typecheck lst gamma))
                (error 'typecheck "expected list"))
              (type-case Type (typecheck lst gamma)
                [listT (x)
                       x]
                [else (error 'typecheck "expected list")])]
      [restl (lst)
             (unless (listT? (typecheck lst gamma))
               (error 'typecheck "expected list"))
             (type-case Type (typecheck lst gamma)
               [listT (x)
                      (typecheck lst gamma)]
               [else (error 'typecheck "expected list")])]
      [nil (typ)
           (listT typ)]
      [mtl? (lst)
            (unless (listT? (typecheck lst gamma))
              (error 'typecheck "expected list"))
            (booleanT)]
      [makevector (size initial)
                  (unless (numberT? (typecheck size gamma))
                    (error 'typecheck "expected number"))
                  (vectorT (typecheck initial gamma))]
      [set (vec index val)
           (unless (vectorT? (typecheck vec gamma))
             (error 'typecheck "expected vector"))
           (unless (numberT? (typecheck index gamma))
             (error 'typecheck "expected number"))
           (type-case Type (typecheck vec gamma)
             [vectorT (x)
                      (if (equal? x (typecheck val gamma))
                          (typecheck val gamma)
                          (error 'typecheck "type mismatch"))]
             [else (error 'typecheck "expected vector")])]
      [lengthl (col)
               (unless (or (vectorT? (typecheck col gamma))
                           (listT? (typecheck col gamma)))
                 (error 'typecheck "expected list or vector"))
               (numberT)]
      [get (col index)
           (unless (or (vectorT? (typecheck col gamma))
                       (listT? (typecheck col gamma)))
             (error 'typecheck "expected list or vector"))
           (unless (numberT? (typecheck index gamma))
             (error 'typecheck "expected number"))
           (type-case Type (typecheck col gamma)
             [listT (x)
                    x]
             [vectorT (x)
                      x]
             [else (error 'typecheck "expected list or vector")])])))

(define typecheck-expr : (TLFAE -> Type)
  (lambda (x)
    (typecheck x (mtEnv))))
      
(define lookup-type : (symbol TypeEnv -> Type)
  (lambda (name gamma)
    (type-case TypeEnv gamma
      [mtEnv () (error 'typecheck "free identifier")]
      [aBind (n2 type rest)
             (if (equal? name n2)
                 type
                 (lookup-type name rest))])))

(define parse : (s-expression -> TLFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (case (s-exp->symbol s-exp)
         [(true)  (bool #t)]
         [(false) (bool #f)]
         [else (id (s-exp->symbol s-exp))])]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid TLFAE")]
             [(s-exp-symbol? (first as-list))
              (case (s-exp->symbol (first as-list))
                [(+)
                 (check-pieces as-list "add" 3)
                 (add (parse (second as-list))
                      (parse (third as-list)))]
                [(-)
                 (check-pieces as-list "sub" 3)
                 (sub (parse (second as-list))
                      (parse (third as-list)))]
                [(=)
                 (check-pieces as-list "eql" 3)
                 (eql (parse (second as-list))
                      (parse (third as-list)))]
                [(if)
                 (check-pieces as-list "if" 4)
                 (ifthenelse (parse (second as-list))
                             (parse (third as-list))
                             (parse (fourth as-list)))]
                [(fun)
                 (check-pieces as-list "fun" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected parameter list"))
                 (define param-list (s-exp->list (second as-list)))
                 (check-pieces param-list "parameter list" 3)
                 (unless (s-exp-symbol? (first param-list))
                   (error 'parse "expected symbol as parameter name"))
                 (unless (and (s-exp-symbol? (second param-list))
                              (equal? ': (s-exp->symbol (second param-list))))
                   (error 'parse "expected `:`"))
                 (fun (s-exp->symbol (first param-list))
                      (parse-type (third param-list))
                      (parse (third as-list)))]
                [(cons)
                 (check-pieces as-list "cons" 3)
                 (consl (parse (second as-list))
                        (parse (third as-list)))]
                [(first)
                 (check-pieces as-list "first" 2)
                 (firstl (parse (second as-list)))]
                [(rest)
                 (check-pieces as-list "rest" 2)
                 (restl (parse (second as-list)))]
                [(nil)
                 (check-pieces as-list "nil" 2)
                 (nil (parse-type (second as-list)))]
                [(empty?)
                 (check-pieces as-list "empty?" 2)
                 (mtl? (parse (second as-list)))]
                [(make-vector)
                 (check-pieces as-list "make-vector" 3)
                 (makevector (parse (second as-list))
                             (parse (third as-list)))]
                [(set)
                 (check-pieces as-list "set" 4)
                 (set (parse (second as-list))
                      (parse (third as-list))
                      (parse (fourth as-list)))]
                [(length)
                 (check-pieces as-list "length" 2)
                 (lengthl (parse (second as-list)))]
                [(get)
                 (check-pieces as-list "get" 3)
                 (get (parse (second as-list))
                      (parse (third as-list)))]
                [else (parse-app as-list)])]
             [else (parse-app as-list)])]
      [else
       (error 'parse "expected TLFAE")])))

(define parse-app : ((listof s-expression) -> TLFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(and (s-exp-symbol? s-exp)
                (equal? 'boolean (s-exp->symbol s-exp)))
           (booleanT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (case (length as-list)
             [(2)
              (unless (s-exp-symbol? (first as-list))
                (error 'parse "expected `listof` or `vectorof`"))
              (case (s-exp->symbol (first as-list))
                [(listof)
                 (listT (parse-type (second as-list)))]
                [(vectorof)
                 (vectorT (parse-type (second as-list)))]
                [else
                 (error 'parse "expected `listof` or `vectorof`")])]
             [(3)
              (unless (and (s-exp-symbol? (second as-list))
                           (equal? '-> (s-exp->symbol (second as-list))))
                (error 'parse "expected `->`"))
              (arrowT (parse-type (first as-list))
                      (parse-type (third as-list)))]
             [else (error 'parse-type "expected type")])]
          [else (error 'parse-type "expected type")])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))