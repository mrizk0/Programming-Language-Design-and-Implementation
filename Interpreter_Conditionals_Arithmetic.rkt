#lang plai

(define-type fnWAE
  [num (n number?)]
  [add (lhs fnWAE?)
       (rhs fnWAE?)]
  [sub (lhs fnWAE?)
       (rhs fnWAE?)]
  [with (name symbol?)
        (bound-expr fnWAE?)
        (body-expr fnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg-expr (listof fnWAE?))]
  [if0 (fn1 fnWAE?)
       (fn2 fnWAE?)
       (fn3 fnWAE?)])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body fnWAE?)])

(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

(define (interp an-fnwae fundefs ds)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs ds) (interp rhs fundefs ds))]
    [sub (lhs rhs)
         (- (interp lhs fundefs ds) (interp rhs fundefs ds))]
    [with (name named-expr body)
          (interp body
                  fundefs
                  (aSub name
                        (interp named-expr fundefs ds)
                        ds))]
    [id (name) (lookup name ds)]
    [if0 (x y z)
         (if (= 0 (interp x fundefs ds))
             (interp y fundefs ds)
             (interp z fundefs ds))]
    [app (fun-name arg-expr)
         (unless (lookup-fundef fun-name fundefs)
           (error 'interp "undefined function"))
         (define arg (map (lambda (x) (interp x fundefs ds)) arg-expr))
         (define the-fundef (lookup-fundef fun-name fundefs))
         (unless (= (length (fundef-param-name the-fundef)) (length arg))
           (error 'interp "wrong arity"))
         (define new-ds
           (new-ds-helper (fundef-param-name the-fundef) arg (mtSub)))
         (interp (fundef-body the-fundef)
                  fundefs
                  new-ds)]))

(define (interp-expr an-fnwae fundefs)
  (interp an-fnwae fundefs (mtSub)))

(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

; helper for interp
(define (new-ds-helper name args ds)
           (if (empty? name)
               ds
               (new-ds-helper (rest name)
                              (rest args)
                              (aSub (first name)
                                    (first args)
                                    ds))))

(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(and (list? s-exp) (not (empty? s-exp)))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [(if0)
            (check-pieces s-exp 4 "if0")
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [else
            (check-pieces (list (first s-exp)) 1 "function application")
            (unless (symbol? (first s-exp))
              (error 'parse "Expected a function name, got: ~a"))
            (app (first s-exp)
                 (map parse (rest s-exp)))])]
        [else
         (error 'parse "expected expression, got: ~a" s-exp)]))

(define (parse-defn quo)
  (if (duplicate? (rest (second quo)))
      (error "bad syntax")
      (fundef (first (second quo))
                 (rest (second quo))
                 (parse (third quo)))))

(define (duplicate? quo)
  (define (dupe quo seen)
    (cond
      [(empty? quo)
       #false]
      [(member (first quo) seen)
       #true]
      [else (dupe (rest quo) (cons (first quo)
                                   seen))]))
  (dupe quo (list)))

(define mult-and-neg-deffuns
  (list
   '{deffun {neg? x} {neg2 x x}}
   '{deffun {mult x y} (if0 {neg? y}
                            (- 0 {mult2 x (- 0 y)})
                            {mult2 x y})}
   '{deffun {mult2 p q} (if0 q
                             0
                             (+ p {mult p (- q 1)}))}
   '{deffun {neg2 p q} (if0 p 1 (if0 q1
                                     0
                                     {neg2 (- p 1)(+ q 1)}))}
   ))
           
;; lookup : symbol? DefSub? -> number?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))