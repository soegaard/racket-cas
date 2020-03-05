#lang racket/base
(provide expand expand-all)

;;;
;;; Expand
;;;

(require racket/list racket/match 
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "logical-operators.rkt" "math-match.rkt" "relational-operators.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require "normalize.rkt" 'normalize))
  (define x 'x) (define y 'y) (define z 'z))


(define (expand u)
  ; expand products and powers with positive integer exponents
  ; expand terms, but don't recurse into sub terms
  ; TODO : implement the above description
  (expand-all u))

(define (expand-all u)
  ; expand products and powers with positive integer exponents, do recurse
  (when verbose-debugging? (displayln (list 'expand-all u)))
  (define e expand-all)
  (define d distribute)
  (math-match u
    [(⊗ @i (⊕ u v))  (⊕ (e (⊗ @i u)) (e (⊗ @i v)))]
    [(⊗ a (⊕ u v))   (e (⊕ (⊗ a u) (⊗ a v)))]
    [(⊗ (⊕ u v) b)   (e (⊕ (⊗ u b) (⊗ v b)))]
    [(⊗ a b)         (let ([ea (e a)] [eb (e b)])
                       (cond [(and (equal? a ea) (equal? b eb))    (⊗  a  b)]
                             [(equal? b eb)                     (e (⊗ ea  b))]
                             [(equal? a ea)                     (e (⊗  a eb))]
                             [else                              (e (⊗ ea eb))]))]
    [(⊕ u v)          (⊕ (e u) (e v))]
    [(Expt (⊕ u v) 2) (e (⊕ (Expt u 2) (Expt v 2) (⊗ 2 u v)))]
    ; TODO: Replace this with a sum the binomial theorem
    [(Expt (⊕ u v) n) #:when (and (>= n 3) (odd? n))
                      (let ([t (e (Expt (⊕ u v) (- n 1)))])
                        (e (⊕ (⊗ u t) (⊗ v t))))]
    [(Expt (⊕ u v) n) #:when (and (>= n 3) (even? n))
                      (let ([t (e (Expt (⊕ u v) (/ n 2)))])
                        (e (⊗ t t)))]
    [(Expt (⊗ u v) w) (e (⊗ (Expt u w) (Expt v w)))]
    [(Ln (Expt u v))  (e (⊗ v (Ln (e u))))]
    [(Equal u v)      (Equal (e u) (e v))]
    [(Or u v)         (Or (e u) (e v))]
    [(And u v)        (And (e u) (e v))]
    ; Note: NSpire doesn't expand arguments of "non builtin functions
    ;       Maxima does. Example to test:     expand( f( (x+1)^3 ) )
    [(app: f us)      (cons f (map e us))]  ; follows maxima
    [_ u]))

(module+ test
  (displayln "TEST - expand")
  (check-equal? (expand (Sqr (⊕ x y))) (⊕ (Sqr x) (Sqr y) (⊗ 2 x y)))
  (check-equal? (expand (Expt (⊕ x y) 4)) (expand (⊗ (Sqr (⊕ x y)) (Sqr (⊕ x y)))))
  (check-equal? (expand (⊗ (⊕ x y) (Cos x))) '(+ (* x (cos x)) (* y (cos x))))
  (check-equal? (expand (Ln (Expt x 3))) (⊗ 3 (Ln x)))
  (check-equal? (expand '(* 2 x (+ 1 x))) (⊕ (⊗ 2 x) (⊗ 2 (Sqr x))))
  (check-equal? (expand '(* (expt (+ 1 x) 2) (sin 2))) 
                '(+ (* 2 x (sin 2)) (* (expt x 2) (sin 2)) (sin 2)))

  (check-equal? (normalize '(+ 2 (* -3 (expt 2 -1) x) (* 3 x))) '(+ 2 (* 3/2 x)))
  (check-equal? (expand-all '(* @i (+ 4 (* -1 (+ (* 4 x) 2))))) '(* @i (+ 2 (* -4 x)))))

