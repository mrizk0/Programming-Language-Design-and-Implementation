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
       (arg-expr (listof fnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body fnWAE?)])

(define (interp an-fnwae fundefs)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs) (interp rhs fundefs))]
    [sub (lhs rhs)
         (- (interp lhs fundefs) (interp rhs fundefs))]
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg-expr)
         (unless (lookup-fundef fun-name fundefs)
           (error 'interp "undefined function"))
         (define arg (map (lambda (x) (interp x fundefs)) arg-expr))
         (define the-fundef (lookup-fundef fun-name fundefs))
         (unless (= (length (fundef-param-name the-fundef)) (length arg))
           (error 'interp "wrong arity"))
         (define body (fundef-body the-fundef))
         (interp (subst2 body
                        (fundef-param-name the-fundef)
                        arg)
                 fundefs)]))

(define (subst2 fnWAE name value)
  (if (or (null? name) (null? value))
      fnWAE
      (subst2 (subst fnWAE (first name)
                     (first value))
              (rest name)(rest value))))

(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

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

;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))

(define (subst a-fnWAE name value)
  (type-case fnWAE a-fnWAE
    [num (n)
         a-fnWAE]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnWAE)]
    [app (fun-name arg-expr)
         (app fun-name (map (lambda (x) (subst x name value)) arg-expr))]))