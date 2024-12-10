#lang plai/gc2/collector

(define (init-allocator)
  (heap-set! 0 (semi)) ; allocation pointer
  (heap-set! 1 1) ; active semi-space
  (heap-set! 2 4) ; left pointer
  (heap-set! 3 4) ; right pointer
  (for ([i (in-range 4 (heap-size))])
    (heap-set! i 'free)))

(define (validate-heap)
  (define start
    (if (= (heap-ref 1) 0)
        4
        (semi)))
  (define (vald s)
    (unless (>= s (heap-ref 0))
      (case (heap-ref s)
        [(flat) (vald (+ s 2))]
        [(cons) (validate-pointer (heap-ref (+ s 1)))
                (validate-pointer (heap-ref (+ s 2)))
                (vald (+ s 3))]
        [(clos) (for ([i (in-range (heap-ref (+ s 2)))])
                  (validate-pointer (heap-ref (+ s 3 i))))
                (vald (+ s 3 (heap-ref (+ s 2))))]
        [(free) (vald (+ s 1))]
        [else (error 'validate-heap "unexpected tag @ ~a" s)])))
  (vald start))

(define (validate-pointer a)
  (unless (and (integer? a)
               (a . >= . 0)
               (a . < . (heap-size))
               (member (heap-ref a) '(flat cons clos)))
    (error 'validate-pointer "invalid pointer @ ~a" a)))

(define (malloc n root1 root2)
  (define z (heap-ref 0))
  (if (equal? (heap-ref 1) 1)
      (if (< (+ n z)
             (heap-size))
          (begin
            (heap-set! 0 (+ n z))
            z)
          (begin
            (collect-garbage root1 root2)
            (let ([z2 (heap-ref 0)])
              (heap-set! 0 (+ n z2))
              (if (equal? (heap-ref 1) 1)
                  (unless (< (heap-ref 0) (heap-size))
                    (error 'malloc "out of memory"))
                  (unless (< (heap-ref 0) (semi))
                    (error 'malloc "out of memory")))
              z2)))
      (if (< (+ n z)
             (semi))
          (begin
            (heap-set! 0 (+ n z))
            z)
          (begin
            (collect-garbage root1 root2)
            (let ([z2 (heap-ref 0)])
              (heap-set! 0 (+ n z2))
              (if (equal? (heap-ref 1) 1)
                  (unless (< (heap-ref 0) (heap-size))
                    (error 'malloc "out of memory"))
                  (unless (< (heap-ref 0) (semi))
                    (error 'malloc "out of memory")))
              z2)))))

(define (collect-garbage root1 root2)
  (validate-heap)
  (traverse/roots (get-root-set))
  (traverse/roots root1)
  (traverse/roots root2)
  (traverse/loc2)
  (swap)
  (validate-heap))

(define (swap)
  (heap-set! 0 (heap-ref 3))
  (if (equal? (heap-ref 1) 0)
      (heap-set! 2 4)
      (heap-set! 3 (semi)))
  (if (equal? (heap-ref 1) 1)
      (heap-set! 2 (semi))
      (heap-set! 3 4))
  (if (equal? (heap-ref 1) 0)
      (heap-set! 1 1)
      (heap-set! 1 0)))

(define (non-fwd roots hep)
  (traverse/loc1 (read-root roots))
  (set-root! roots hep))

(define (traverse/roots roots)
  (cond [(false? roots)
         (void)]
        [(list? roots) (for-each traverse/roots roots)]
        [(root? roots)
         (if (symbol=? (heap-ref (read-root roots)) 'f)
             (set-root! roots (heap-ref (+ 1 (read-root roots))))
             (non-fwd roots (heap-ref 3)))]
        [(number? roots)
         (traverse/loc1 roots)]
        [else
         (error 'traverse/roots "unexpected root: ~a" roots)]))

(define (traverse/loc1 ptr)
  (case (heap-ref ptr)
    [(free)
     (error "dangling pointer!")]
    [(flat)
     (heap-set! (heap-ref 3) 'flat)
     (heap-set! (+ 1 (heap-ref 3)) (heap-ref (+ 1  ptr)))
     (heap-set! ptr 'f)
     (heap-set! (+ 1 ptr) (heap-ref 3))
     (heap-set! 3 (+ 2 (heap-ref 3)))]
    [(cons)
     (heap-set! (heap-ref 3) 'cons)
     (heap-set! (+ 1 (heap-ref 3)) (heap-ref (+ 1 ptr)))
     (heap-set! (+ 2 (heap-ref 3)) (heap-ref (+ 2 ptr)))
     (heap-set! ptr 'f)
     (heap-set! (+ 1 ptr) (heap-ref 3))
     (heap-set! 3 (+ 3 (heap-ref 3)))]
    [(clos)
     (heap-set! (heap-ref 3) 'clos)
     (heap-set! (+ 1 (heap-ref 3)) (heap-ref (+ 1 ptr)))
     (heap-set! (+ 2 (heap-ref 3)) (heap-ref (+ 2 ptr)))
     (define n-free-vars (heap-ref (+ 2 ptr)))
     (for ([i (in-range n-free-vars)])
       (heap-set! (+ 3 i (heap-ref 3)) (heap-ref (+ 3 ptr i))))
     (heap-set! ptr 'f)
     (heap-set! (+ 1 ptr) (heap-ref 3))
     (heap-set! 3 (+ 3 n-free-vars (heap-ref 3)))]
    [else (error "unexpected tag")]))

(define (traverse/loc2)
  (if (> (heap-ref 2) (heap-ref 3))
      (error "traversal error")
      (if (not (equal? (heap-ref 2) (heap-ref 3)))
          (case (heap-ref (heap-ref 2))
            [(free)
             (error "dangling pointer!")]
            [(flat)
             (heap-set! 2 (+ 2 (heap-ref 2)))
             (traverse/loc2)]
            [(cons)
             (if (symbol=? (heap-ref (heap-ref (+ 1 (heap-ref 2)))) 'f)
                 (heap-set! (+ 1 (heap-ref 2)) (heap-ref (+ 1 (heap-ref (+ 1 (heap-ref 2))))))
                 (begin
                   (let ([a (heap-ref 3)])
                     (traverse/loc1 (heap-ref (+ (heap-ref 2) 1)))
                     (heap-set! (+ 1 (heap-ref 2)) a))))
             (if (symbol=? (heap-ref (heap-ref (+ 2 (heap-ref 2)))) 'f)
                 (heap-set! (+ 2 (heap-ref 2)) (heap-ref (+ 1 (heap-ref (+ 2 (heap-ref 2))))))
                 (begin
                   (let ([a (heap-ref 3)])
                     (traverse/loc1 (heap-ref (+ 2 (heap-ref 2))))
                     (heap-set! (+ 2 (heap-ref 2)) a))))
             (heap-set! 2 (+ 3 (heap-ref 2)))
             (traverse/loc2)]
            [(clos)
             (define n-free-vars (heap-ref (+ 2 (heap-ref 2))))
             (for ([i (in-range (heap-ref (+ (heap-ref 2) 2)))])
               (if (symbol=? (heap-ref (heap-ref (+ 3 i (heap-ref 2)))) 'f)
                   (heap-set! (+ 3 i (heap-ref 2)) (heap-ref (+ 1 (heap-ref (+ 3 i (heap-ref 2))))))
                   (begin
                     (let ([a (heap-ref 3)])
                       (traverse/loc1 (heap-ref (+ 3 i (heap-ref 2))))
                       (heap-set! (+ 3 i (heap-ref 2)) a)))))
             (heap-set! 2 (+ 3 n-free-vars (heap-ref 2)))
             (traverse/loc2)]
            [else (error "unexpected tag")])
          (void))))

(define (semi)
  (+ (/ (- (heap-size) 4) 2) 4))

;; gc:alloc-flat : flat-value -> location
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : location -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : location -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))

;; gc:cons : root root -> location
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : location -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : location -> location
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : location -> location
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : location location -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : location location -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) ->  location
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars))
                          free-vars #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([i  (in-range (length free-vars))]
        [fv (in-list free-vars)])
    (heap-set! (+ address 3 i) (read-root fv)))
  address)
;; gc:closure? :  location -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : location -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : location integer -> location
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 3 i)))