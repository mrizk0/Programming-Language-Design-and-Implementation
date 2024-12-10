#lang plai

(define-type EFAE
  [num (n number?)]
  [add (lhs EFAE?)
       (rhs EFAE?)]
  [sub (lhs EFAE?)
       (rhs EFAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body EFAE?)]
  [app (fun-expr EFAE?)
       (arg-expr EFAE?)]
  [if0 (tst EFAE?)
       (thn EFAE?)
       (els EFAE?)]
  [throw (tag symbol?)
         (throw-expr EFAE?)]
  [try-catch (try-body EFAE?)
             (tag symbol?)
             (exn-name symbol?)
             (catch-body EFAE?)])

(define-type EFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body EFAE?)
            (ds DefSub?)])
(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value EFAE-Value?)
         (rest DefSub?)])

;; parse : s-expression -> EFAE
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "expected function"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp "with" 3)
            (check-pieces (second s-exp) "with binding pair" 2)
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got ~a" (first (second s-exp))))
            (app (fun (first (second s-exp)) (parse (third s-exp)))
                 (parse (second (second s-exp))))]
           [(if0)
            (check-pieces s-exp "if0" 4)
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [(throw)
            (check-pieces s-exp "throw" 3)
            (throw (second s-exp)
                   (parse (third s-exp)))]
           [(try)
            (check-pieces s-exp "try" 3)
            (check-pieces (third s-exp) "catch" 3)
            (try-catch (parse (second s-exp))
                       (second (second (third s-exp)))
                       (fourth (second (third s-exp)))
                       (parse (third (third s-exp))))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected function")]))

;; interp : EFAE? DefSub?
;;    (EFAE-Value? -> EFAE-Value?)
;;    (EFAE-Value? -> EFAE-Value?)
;;    -> EFAE-Value?
(define (interp a-efae ds k ret-k)
  (type-case EFAE a-efae
    [num (n) (k (numV n))]
    [id (name) (k (lookup name ds))]
    [fun (param-name body) (k (closureV param-name body ds))]
    [add (l r) (numop + l r ds k ret-k)]
    [sub (l r) (numop - l r ds k ret-k)]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (interp arg-expr ds
                           (lambda (arg-val)
                             (type-case EFAE-Value fun-val
                               [closureV (param-name body ds2)
                                         (interp body
                                                 (aSub param-name
                                                       arg-val
                                                       ds2)
                                                 (lambda (ret-val)
                                                   (k ret-val))
                                                 ret-k)]
                               [else (error 'interp "expected function")]))
                           ret-k)) ret-k)]
    [if0 (tst thn els)
         (interp tst ds
                 (lambda (test)
                   (type-case EFAE-Value test
                     [numV (n)
                           (if (zero? n)
                               (interp thn ds
                                       (lambda (then)
                                         (k then)) ret-k)
                               (interp els ds
                                       (lambda (else)
                                         (k else)) ret-k))]
                     [closureV (param-name body ds2)
                               (interp els ds2
                                       (lambda (else2)
                                         (k else2)) ret-k)])) ret-k)]
    [throw (tag throw-expr)
           (interp throw-expr ds
                   (lambda (x)
                     (ret-k tag x))
                   ret-k)]
    [try-catch (try-body tag exn-name catch-body)
               (interp try-body ds k
                       (lambda (y z)
                         (if (equal? y tag)
                             (interp catch-body
                                     (aSub exn-name z ds)
                                     k
                                     ret-k)
                             (ret-k y z))))]))

;; interp-expr : EFAE -> number or ’function
(define (interp-expr a-efae)
  (type-case EFAE-Value
    (interp a-efae
            (mtSub)
            (lambda (v) v)
            (lambda (x y) (error "missing catch")))
    [numV (n) n]
    [closureV (param-name body ds) 'function]))



(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;; lookup : symbol? DefSub? -> KFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error "free identifier")]
    [aSub (name2 value rest)
          (if (equal? name name2)
              value
              (lookup name rest))]))

;; numop : (number? number? -> number?) KFAE? KFAE? DefSub?
;;         (KFAE-Value? -> KFAE-Value?)
;;         (KFAE-Value? -> KFAE-Value?)
;;            -> KFAE-Value?
(define (numop op l r ds k ret-k)
  (interp l ds
          (lambda (l-val)
            (interp r ds
                    (lambda (r-val)
                      (unless (and (numV? l-val) (numV? r-val))
                        (error 'interp "expected number"))
                      (k (numV (op (numV-n l-val) (numV-n r-val)))))
                    ret-k))
          ret-k))