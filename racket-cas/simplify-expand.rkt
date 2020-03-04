#lang racket/base
(provide subst          ; (subst u v w #:normalize? [normalize? #t])   ; substitute w for v in u
         subst*
         logical-expand
         simplify)

;;;
;;; Simplification / Expansion / Substitution
;;;

; This module contains functions that manipulate expressions.


(require racket/match "core.rkt" "diff.rkt" "math-match.rkt"  "parameters.rkt")
(define normalize (dynamic-require "normalize.rkt" 'normalize))

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))


;;; Substition

(define (subst u v w #:normalize? [normalize? #t]) ; substitute w for v in u
  (define le logical-expand)
  (define (n* us) (map normalize us))
  (define (s u)
    (math-match u
      [u #:when (equal? u v) w]
      [(⊕ u1 u2)          (⊕ (s u1) (s u2))]
      [(⊗ u1 u2)          (⊗ (s u1) (s u2))]
      [(Expt u1 u2)       (Expt (s u1) (s u2))]
      [(Piecewise us vs)  (Piecewise: (n* (map s us)) (n* (map s vs)))]
      [(And u v)          (And (le (s u)) (le (s v)))] ; xxx is le needed?
      [(Or  u v)          (Or  (le (s u)) (le (s v)))]
      [(Equal u v)        (Equal (s u) (s v))]         ; xxx
      [(Less u v)         (Less (s u) (s v))]
      [(LessEqual u v)    (LessEqual (s u) (s v))]
      [(Greater u v)      (Greater (s u) (s v))]
      [(GreaterEqual u v) (GreaterEqual (s u) (s v))]
      
      [(app: f us)       `(,f ,@(map s us))]
      [_ u]))
  (if normalize?
      (normalize (s u))
      (s u)))


(module+ test
  (displayln "TEST - subst")
  (check-equal? (subst '(expt (+ (* x y) 1) 3) y 1) '(expt (+ 1 x) 3))
  (check-equal? (let () (define (f x) '(expt (+ x 1) 3)) (subst (f x) x 1)) 8))

(define (subst* u vs ws)
  ; in u substitute each expression in vs with the corresponding expression in ws
  (for/fold ([u u]) ([v vs] [w ws])
    (subst u v w)))

(module+ test (check-equal? (subst* '(+ 1 x y z) '(x y) '(a b)) '(+ 1 a b z)))



(define (logical-expand u)
  (define u0 u)
  (define le logical-expand)
  (math-match u
    [(And #f u)          #f]
    [(And #t u)          (le u)]
    [(And u (Or v1 v2))  (Or (le (And v1 u)) (le (And v2 u)))]
    [(Or u v)            (Or (le u) (le v))]

    [(or (And (Equal x u) v)
         (And v (Equal x u))) (match (simplify (subst v x u))
                                [#t (Equal x u)]
                                [#f #f]
                                [_  (And (Equal x u) (le v))])]
    [u                   u]))

(define (simplify u) ; use when the automatic simplification isn't enough
  ; TODO: rewrite fractions with square roots in the denominator
  (define s simplify)
  (math-match u
    [(Expt n 1/2)    (Expt n 1/2)]
    [(⊗ u v)         (⊗ (s u) (s v))]
    [(⊕ u v)         (⊕ (s u) (s v))]
    [(list (var: op) r1 r2) (case op
                              [(=)  (=  r1 r2)]
                              [(<)  (<  r1 r2)]
                              [(>)  (>  r1 r2)]
                              [(<=) (<= r1 r2)]
                              [(>=) (>= r1 r2)]
                              [else u])]
    [(Equal u1 u2)   (Equal (s u1) (s u2))]
    [(Diff u x)      (diff u x)]
    [_ u]))

(module+ test (check-equal? (simplify '(+ 3 (* 2 (expt 8 1/2))))
                            (⊕ (⊗ 2 2 (Sqrt 2)) 3)))


;;; Parameter Initialization
; The core can't require the simplify module (modules don't allow cycles),
; so the core looks for simplify in the parameter current-simplify.

(current-simplify simplify)
