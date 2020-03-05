#lang racket/base
(provide trig-expand)

;;;
;;; Trig Expand
;;; 

(require racket/match racket/math
         (only-in math/number-theory binomial)
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "expand.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))



; rewrite sin(n*u) and cos(n*u) in terms of cos(u) and sin(u)
; rewrite cos(u+v) and sin(u+v) in terms of cos(u),cos(v),sin(u) and sin(v)
(define (trig-expand u)  
  (define (t u)
    (math-match u
      [r r]
      [r.bf r.bf]
      [x x]
      [(⊕ u v) (⊕ (t u) (t v))]
      [(⊗ u v) (⊗ (t u) (t v))]
      [(Sin 0) 0]
      [(Sin (⊗ n u)) #:when (negative? n)
                     (⊖ (t (Sin (- n) u)))]
      [(Sin (⊗ n u)) (for/⊕ ([k (in-range (+ n 1))])
                            (⊗ (binomial n k) 
                               (Expt (Cos u) k)
                               (Expt (Sin u) (- n k))
                               (sin-pi/2* (- n k))))]
      [(Cos 0) 1]
      [(Cos (⊗ n u)) #:when (negative? n)
                     (t (Cos (- n) u))]
      [(Cos (⊗ n u)) (for/⊕ ([k (in-range (+ n 1))])
                            (⊗ (binomial n k)
                               (Expt (Cos u) k)
                               (Expt (Sin u) (- n k))
                               (cos-pi/2* (- n k))))]
      [(Sin (⊕ u v)) (t (⊕ (⊗ (Sin u) (Cos v))  (⊗ (Sin v) (Cos u))))]
      [(Cos (⊕ u v)) (t (⊖ (⊗ (Cos u) (Cos v))  (⊗ (Sin u) (Sin v))))]
      [(Expt u n)  (expand (Expt (t u) n))]
      [(app: f us) `(,f ,@(map t us))]
      [_ u]))
  (t u))

(module+ test
  (displayln "TEST - trig-expand")
  (check-equal? (trig-expand (Sin (⊗ 2 x))) (⊗ 2 (Cos x) (Sin x)))
  (check-equal? (trig-expand (Cos (⊗ 2 x))) (⊖ (Sqr (Cos x)) (Sqr (Sin x))))
  (let ([u 'u] [v 'v])
    (check-equal? (trig-expand (Sin (⊕ u v))) (⊕ (⊗ (Sin u) (Cos v))  (⊗ (Sin v) (Cos u))))
    (check-equal? (trig-expand (Cos (⊕ u v))) (⊖ (⊗ (Cos u) (Cos v))  (⊗ (Sin u) (Sin v))))
    (check-equal? (trig-expand '(expt (sin (* 2 x)) 2)) '(* 4 (expt (cos x) 2) (expt (sin x) 2)))))
