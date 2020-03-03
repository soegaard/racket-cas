#lang racket/base
;;;
;;; Limits
;;;

(provide limit) ; (limit u x x0)  compute the limit of the expression for x -> x0

         
(require "core.rkt" "math-match.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))


; (limit u x x0) computes the limit of the expression u for a variable x going towards x0
(define (limit u x x0)
  (let/ec return
    (define (l u)
      (math-match u
        [r r]
        [y #:when (eq? x y) x0]
        [y y]
        [(⊕ v w) (⊕ (l v) (l w))]
        [(⊘ v w) (let loop ([n 1] [v v] [w w])
                   (let ([lv (l v)] [lw (l w)])
                     ; if both limits are zero, use l'Hôpital's rule
                     (define (again) (loop (+ n 1) (diff v x) (diff w x)))
                     (define (give-up) (return `(limit ,u ,x ,x0)))
                     (if (= n 10) 
                         (give-up)
                         (math-match* (lv lw)
                           [(0 0) (again)]
                           [(r 0) (return +nan.0)]
                           [(r s) (/ r s)]
                           [(_ _) (give-up)]))))]
        [(⊗ v w) (⊗ (l v) (l w))]
        [(Expt u v) (math-match* ((l u) (l v))
                      [(0 r) #:when (negative? r) (return +nan.0)]
                      [(0 0) 1] ; TODO: compare to other CAS.
                      [(0 r) 0]
                      [(u v) (Expt u v)])]
        ; TODO: need a lookup table for function names to determine, whether they are continous
        [(Sin u) (Sin (l u))]
        [(Cos u) (Cos (l u))]
        [(Ln u)  (Ln  (l u))]
        [_ `(limit ,u ,x ,x0)]))
    (l u)))

(module+ test
  (displayln "TEST - limit")
  (check-equal? (limit 1 x 0) 1)
  (check-equal? (limit x x 0) 0)
  (check-equal? (limit y x 0) y)
  (check-equal? (limit (⊗ 2 x) x 3) 6)
  (check-equal? (limit (⊕ 2 x) x 3) 5)
  (check-equal? (limit (Expt (⊕ 'h x) 3) 'h 0) '(expt x 3))
  (check-equal? (limit (Expt 3 (⊕ 'h x)) 'h 0) '(expt 3 x))
  (check-equal? (limit (Sin x) x y) '(sin y))
  ; Now for the tricky ones:
  (check-equal? (limit (⊘ (Sin x) x) x 0) 1)
  (check-equal? (limit (⊘ (⊖ (Sqr x) 1) (⊖ x 1)) x 1) 2))

; Note: (limit (⊘ (⊖ (Sqr x) 4) (⊖ x 2)) x 2) gives 0
; Cause: (⊗ 0 +inf.0) currently gives 0.
