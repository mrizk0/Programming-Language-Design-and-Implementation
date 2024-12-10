#lang plai

(define-type FAE
    [num (n number?)]
    [add (lhs FAE?) (rhs FAE?)]
    [sub (lhs FAE?) (rhs FAE?)]
    [id (name symbol?)]
    [if0 (test FAE?) (then FAE?) (else FAE?)]
    [fun (param symbol?) (body FAE?)]
    [app (fun FAE?) (arg FAE?)])

(define-type FNWAE
    [W-num (n number?)]
    [W-add (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-sub (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-with (name symbol?)
            (named-expr FNWAE?)
            (body FNWAE?)]
    [W-id (name symbol?)]
    [W-if0 (tst FNWAE?)
           (thn FNWAE?)
           (els FNWAE?)]
    [W-fun (params (listof symbol?))
           (body FNWAE?)]
    [W-app (fun-expr  FNWAE?)
           (arg-exprs (listof FNWAE?))])

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub (name  symbol?)
        (value FAE-Value?)
        (rest  DefSub?)])

; compile : FNWAE? -> FAE?
(define (compile an-FNWAE)
  (type-case FNWAE an-FNWAE
        [W-num (n) (num n)]
    [W-id (name) (id name)]
    [W-add (l r)
           (try-constant-fold
            (add (compile l)
                 (compile r)))]
    [W-sub (l r)
           (try-constant-fold
            (sub (compile l)
                 (compile r)))]
    [W-fun (param body)
           (if (empty? param)
               (error "nullary function")
               (if (empty? (rest param))
                   (fun (first param) (compile body))
                   (fun (first param) (compile (W-fun (rest param) body)))))]
    [W-app (f arg)
           (if (empty? f)
               (error "nullary application")
               (app-compile (compile f) arg))]
    [W-with (name named-expr body)
            (app (fun name (compile body))
                 (compile named-expr))]
    [W-if0 (tst thn els) (if0 (compile tst) (compile thn) (compile els))]))
    

(define (app-compile f arg)
  (if (empty? arg)
      (error "nullary application")
      (if (empty? (rest arg))
          (app f (compile (first arg)))
          (app-compile (app f (compile (first arg))) (rest arg)))))

;; interp : FAE? DefSub? -> FAE-Value?
(define (interp an-fae ds)
  (type-case FAE an-fae
    [num (n) (numV n)]
    [add (l r) (numop + l r ds)]
    [sub (l r) (numop - l r ds)]
    [id (name) (lookup name ds)]
    [fun (param-name body) (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (unless (closureV? fun-val)
             (error "expected function"))
         (define arg-val (interp arg-expr ds))
         (type-case FAE-Value fun-val
           [closureV (param-name body closed-ds)
                     (interp body
                             (aSub param-name
                                   arg-val
                                   closed-ds))]
           [else (error 'interp "expected function")])]
    [if0 (tst thn els)
         (if (equal? (interp tst ds) (numV 0))
             (interp thn ds)
             (interp els ds))]))

(define (numop op l r ds)
  (define l-val (interp l ds))
  (define r-val (interp r ds))
  (unless (and (numV? l-val) (numV? r-val))
    (error "expected number"))
  (numV (op (numV-n l-val) (numV-n r-val))))

(define (interp-expr an-fae)
  (define intr (interp an-fae (mtSub)))
  (type-case FAE-Value intr
    [numV (n) n]
    [closureV (param body ds) 'function]))

;; FAE? -> FAE?
(define (try-constant-fold an-fae)
  ;; Local function definition: we can refer to `an-fae`
  (define (try-fold-op op l r)
    (if (and (num? l)
             (num? r))
        (num (op (num-n l) (num-n r)))
        an-fae))
  (type-case FAE an-fae
    [add (l r)
         (try-fold-op + l r)]
    [sub (l r)
         (try-fold-op - l r)]
    [else an-fae]))

;; lookup : symbol? DefSub? -> FAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier: ~a" name)]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))


;; parse : s-expr -> FNWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (W-num s-expr)]
        [(symbol? s-expr)
         (W-id s-expr)]
        [(list? s-expr)
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (W-add (parse (second s-expr))
                   (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (W-sub (parse (second s-expr))
                   (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (W-with (first (second s-expr))
                    (parse (second (second s-expr)))
                    (parse (third s-expr)))]
           [(fun)
            (check-pieces s-expr 3 "fun")
            (W-fun (second s-expr)
                   (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "fun")
            (W-if0 (parse (second s-expr))
                   (parse (third s-expr))
                   (parse (fourth s-expr)))]
           [else
            (check-pieces (list (first s-expr)) 1 "app")
            (W-app (parse (first s-expr)) (map parse (rest s-expr)))])]))


(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))


(define factorial
  `{with {helper1 {fun {helper1 x y}
                       {if0 y
                            0
                            {+ x {helper1 helper1 x {- y 1}}}}}}
         {with {helper2 {fun {helper2 p q}
                             {if0 p
                                  q
                                  {helper2 helper2 {- p 1} {helper1 helper1 p q}}}}}
               {with {helper3 {fun {helper3 a} {helper2 helper2 a 1}}}
                     {fun {b} {helper3 helper3 b}}}}})

(define prime?
  `{with {helper1
          {fun {helper1 x y}
               {if0 y
                    0
                    {+ x {helper1 helper1 x {- y 1}}}}}}
         {with {helper2
                {fun {a b c}
                     {if0 {- b 1}
                          1
                          {if0 {- b c}
                               0
                               {if0 {- b {helper1 helper1 c 2}}
                                    1
                                    {if0 {- b {helper1 helper1 c 3}}
                                         1
                                         {if0 {- b {helper1 helper1 c 5}}
                                              1
                                              {if0 {- b {helper1 helper1 c 7}}
                                                   1
                                                   {a a b {+ c 1}}}}}}}}}}
               {fun {p}
                    {helper2 helper2 p 2}}}})