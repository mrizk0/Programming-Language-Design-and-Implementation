#lang plai

(define-type SFAE
  [num (n number?)]
  [add (lhs SFAE?) (rhs SFAE?)]
  [sub (lhs SFAE?) (rhs SFAE?)]
  [id (name symbol?)]
  [structer (x (listof (cons/c symbol? SFAE?)))]
  [get (x SFAE?) (y symbol?)]
  [setter (x SFAE?) (y symbol?) (z SFAE?)]
  [fun (param symbol?) (body SFAE?)]
  [app (fun SFAE?) (arg SFAE?)]
  [seqn (x SFAE?) (y SFAE?)])

(define-type SFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body SFAE?)
            (ds DefSub?)]
  [structV (addr number?)])

(define-type Store
  [mtSto]
  [aSto (id symbol?)
        (address integer?)
        (value SFAE-Value?)
        (rest Store?)])
(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value SFAE-Value?)
         (rest DefSub?)])

(define-type Value*Store
  [v*s (v SFAE-Value?)
       (s Store?)])

(define (interp an-SFAE ds st)
  (type-case SFAE an-SFAE
    [num (n) (v*s (numV n)
                  st)]
    [add (l r)
         (let* ([l2 (interp l ds st)]
                [lv (v*s-v l2)]
                [st2 (v*s-s l2)]
                [r2 (interp r ds st2)]
                [rv (v*s-v r2)]
                [st3 (v*s-s r2)])
           (v*s (numop + lv rv ds st3) st3))]
    [sub (l r)
         (let* ([l2 (interp l ds st)]
                [lv (v*s-v l2)]
                [st2 (v*s-s l2)]
                [r2 (interp r ds st2)]
                [rv (v*s-v r2)]
                [st3 (v*s-s r2)])
           (v*s (numop - lv rv ds st3)
                st3))]
    [id (name)
        (v*s (lookup name ds)
             st)]
    [fun (param-name body)
         (v*s (closureV param-name body ds)
              st)]
    [app (fun-expr arg-expr)
         (interp-two fun-expr arg-expr ds st
                     (lambda (fun-val arg-val st3)
                       (unless (closureV? fun-val)
                         (error 'interp "expected function"))
                       (interp (closureV-body fun-val)
                               (aSub (closureV-param-name fun-val)
                                     arg-val
                                     (closureV-ds fun-val))
                               st3)))]
    [structer (x)
          (if (empty? x)
              (let ([addr (type-case Store st
                           [mtSto () 0]
                           [aSto (i a v r) a])])
                (v*s (structV addr) st))
              (let* ([x1 (first x)]
                     [x1-1 (car x1)]
                     [x1-2 (cdr x1)]
                     [x-int (interp x1-2 ds st)]
                     [x-v (v*s-v x-int)]
                     [x-s (v*s-s x-int)]
                     [addr (malloc x-s)]
                     [st2 (aSto x1-1 addr x-v x-s)])
                (interp (structer (rest x)) ds st2)))]
    [get (x y)
      (let ([x-int (interp x ds st)])
        (if (Value*Store? x-int)
            (let ([x-v (v*s-v x-int)]
                  [x-s (v*s-s x-int)])
              (if (structV? x-v)
                  (let ([val (find_struct_val x-s (structV-addr x-v) y)])
                    (v*s val x-s))
                  (error "expected struct")))
            (error "expected struct")))]

    [setter (x y z)
            (let ([x-int (interp x ds st)])
              (if (Value*Store? x-int)
                  (let* ([x-v (v*s-v x-int)]
                         [x-s (v*s-s x-int)])
                    (if (structV? x-v)
                        (let* ([addr (structV-addr x-v)]
                               [z-int (interp z ds x-s)]
                               [z-v (v*s-v z-int)]
                               [z-s (v*s-s z-int)]
                               [old-val (find_struct_val z-s addr y)]
                               [new-store (update_st z-s addr y z-v)])
                          (v*s old-val new-store))
                        (error "expected struct")))
                  (if (structV? x-int)
                      (let* ([addr (structV-addr x-int)]
                             [z-int (interp z ds st)]
                             [z-v (v*s-v z-int)]
                             [z-s (v*s-s z-int)]
                             [old-val (find_struct_val z-s addr y)]
                             [new-store (update_st z-s addr y z-v)])
                        (v*s old-val new-store))
                      (error "expected struct"))))]         
    [seqn (x y)
          (let* ([x-int (interp x ds st)]
                 [x-v (v*s-v x-int)]
                 [x-s (v*s-s x-int)])
            (let ([y-int (interp y ds x-s)])
              (let ([y-v (v*s-v y-int)]
                    [y-s (v*s-s y-int)])
                (v*s y-v y-s))))]))
  
(define (interp-expr an-sfae)
  (let* ([inp (interp an-sfae (mtSub) (mtSto))]
         [v1 (v*s-v inp)])
    (cond
      [(numV? v1)
       (numV-n v1)]
      [(structV? v1)
       'struct]
      [(closureV? v1)
       'function]
      [else (error "free identifier")])))

;; interp-two : BFAE? BFAE? DefSub? Store?
;;              (BFAE-Value? BFAE-Value? Store? -> Value*Store?)
;;              -> Value*Store?
(define (interp-two e1 e2 ds st finish)
  (type-case Value*Store (interp e1 ds st)
            [v*s (v1 st2)
                 (type-case Value*Store (interp e2 ds st2)
                   [v*s (v2 st3)
                        (finish v1 v2 st3)])]))

(define (numop op l r ds st)
  (unless (and (numV? l) (numV? r))
    (error 'interp "expected number"))
  (numV (op (numV-n l) (numV-n r))))

;; lookup : symbol? DefSub? -> BFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

(define (find_st st n)
  (cond [(mtSto? st)
         (error "unknown field")]
        [(aSto? st)
         (if (equal? n (aSto-address st))
             st
             (find_st (aSto-rest st) n))]))

(define (find_val st id)
  (cond [(mtSto? st)
         (error "unknown field")]
        [(aSto? st)
         (if (equal? id (aSto-id st))
             (aSto-value st)
             (find_val (aSto-rest st) id))]))

(define (find_struct_val st addr id)
  (let ([struct-store (find_st st addr)])
    (find_val struct-store id)))

(define (update_st st addr fld val)
  (cond
    [(mtSto? st) 
     (aSto fld addr val (mtSto))]
    [(aSto? st)
     (let ([curr-addr (aSto-address st)])
       (if (= addr curr-addr)
           (aSto fld addr val (aSto-rest st))
           (aSto (aSto-id st)
                 (aSto-address st)
                 (aSto-value st)
                 (update_st (aSto-rest st) addr fld val))))]))

;; parse : s-expr -> SFAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (num s-expr)]
        [(symbol? s-expr)
         (id s-expr)]
        [(list? s-expr)
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (add (parse (second s-expr))
                   (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (sub (parse (second s-expr))
                   (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (app (fun (first (second s-expr))
                      (parse (third s-expr)))
                 (parse (second (second s-expr))))]
           [(fun)
            (check-pieces s-expr 3 "fun")
            (check-pieces (second s-expr) 1 "parameter list")
            (fun (first (second s-expr))
                 (parse (third s-expr)))]
           [(struct)
            (for ([x (rest s-expr)])
              (check-pieces x 2 "struct"))
            (structer (for/list ([i (in-list (rest s-expr))])
                        (cons (first i) (parse (last i)))))]
           [(get)
            (check-pieces s-expr 3 "get")
            (get (parse (second s-expr)) (third s-expr))]
           [(set)
            (check-pieces s-expr 4 "set")
            (setter (parse (second s-expr)) (third s-expr) (parse (fourth s-expr)))]
           [(seqn)
            (seqn (parse (second s-expr)) (parse (third s-expr)))]
           [else
            (check-pieces s-expr 2 "app")
            (app (parse (first s-expr)) (parse (second s-expr)))])]))

(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

;; malloc : Store? -> integer?
(define (malloc st)
  (+ 1 (max-address st)))

(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (i a v r) (max a (max-address r))]))