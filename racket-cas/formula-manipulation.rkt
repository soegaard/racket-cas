#lang racket/base
(provide together
         combine
         QuotientTogether
         mma-numerator/denominator)

;;;
;;; Formula Manipulation
;;;

(require racket/match 
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "runtime-paths.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require normalize.rkt 'normalize))
  (define x 'x) (define y 'y) (define z 'z))

;;;
;;; Formula Manipulation
;;;



;;; Together

; The `together` operations rewrites a sum into a single fraction.
; A common denominator the terms in the sum is found.


(define (together u)
  (when debugging? (displayln (list 'together u)))
  (parameterize ([lazy-expt? #t])
    (together-impl u)))

(define (together-impl expr)
  (define t together-impl)
  (math-match expr
    [(⊕ u v) (together-op2 u (t v))]
    [_       expr]))

(define (together-op2 u v)
  (define-values (nu du) (numerator/denominator u))
  (define-values (nv dv) (numerator/denominator v))
  (if (equal? du dv)
      (⊘ (⊕ nu nv) du)
      (⊘ (⊕ (⊗ nu dv) (⊗ nv du))
         (⊗ du dv))))


(module+ test 
  (displayln "TEST - together")
  (lazy-expt? #t)
  (check-equal? (together (⊕ (⊘ `a `b) (⊕ y x)))                    '(* (expt b -1) (+ a (* b (+ x y)))))
  (check-equal? (together (⊕ (⊘ `a `b) (⊘ `c `d) (⊘ `e `f)))        '(* (expt (* b d f) -1)
                                                                        (+ (* a d f)
                                                                           (* b (+ (* c f) (* d e))))))
  (check-equal? (together (⊕ (⊘ 7 2) (⊘ 3 5)))                      '41/10)
  (check-equal? (together (⊕ (⊘ 7 x) (⊘ y 5) 1))                    '(* (expt (* 5 x) -1) (+ 35 (* x y) (* 5 x))))
  (check-equal? (together (⊕ (⊘ 2 y) (⊘ 1 x)))                      '(* (expt (* x y) -1) (+ (* 2 x) y)))
  (check-equal? (together (⊕ (⊘ 1 x) (⊘ 2 y)))                      '(* (expt (* x y) -1) (+ (* 2 x) y)))
  (check-equal? (together (plus (⊘ (⊗ y 3) x) (⊘ (⊗ x z 1/3) 5/6))) '(* (expt (* 5 x) -1)
                                                                        (+ (* 2 (expt x 2) z) (* 15 y))))

  (parameterize ([lazy-expt? #t])
    (check-equal? (together (normalize '(+ (/ y 5) 1))) '(* 1/5 (+ 5 y))))
  (real-mode))

; test cases adapted from https://reference.wolfram.com/language/ref/Together.html?view=all
(module+ test 
  (check-equal? (together (⊕ (⊘ 'a 'b) (⊘ 'c 'd))) '(* (expt (* b d) -1) (+ (* a d) (* b c))))
  ; todo: '(* (expt (+ -1 (expt x 2)) -1) (+ x (expt x 2))) should be simplified as (* (expt (+ -1 x) -1) x)
  (check-equal? (together (⊕ (⊘ (Expt x 2) (⊖ (Expt x 2) 1)) (⊘ x (⊖ (Expt x 2) 1)))) '(* (expt (+ -1 (expt x 2)) -1) (+ x (expt x 2))))
  ; todo: should simplify numerator. expand -> '(+ 6 (* 22 x) (* 18 (expt x 2)) (* 4 (expt x 3))) -> further factorize 2
  (check-equal? (together (⊕ (⊘ 1 x) (⊘ 1 (⊕ x 1)) (⊘ 1 (⊕ x 2))  (⊘ 1 (⊕ x 3))))
                '(* (expt (* x (+ 1 x) (+ 2 x) (+ 3 x)) -1) (+ (* x (+ (* (+ 1 x) (+ 5 (* 2 x))) (* (+ 2 x) (+ 3 x)))) (* (+ 1 x) (+ 2 x) (+ 3 x)))))
  ; todo: cancels common factors.
  (check-equal? (together (⊕ (⊘ (Expt x 2) (⊖ x y)) (⊘ (⊖ (⊗ x y)) (⊖ x y))))
                '(* (expt (+ x (* -1 y)) -1) (+ (expt x 2) (* -1 x y))))
  ; Together[1 < 1/x + 1/(1 + x) < 2] not supported.
  ; Apart acts as a partial inverse of Together:
  ; Cancel only cancels common factors between numerators and denominators:
  )

; combine (Maxima) : a/c + b/c = (a+b)/c
;   Simplifies the sum expr by combining terms with the same denominator into a single term.
(define (combine expr)
  (when debugging? (displayln (list 'combine expr)))
  (define c combine)
  (math-match expr
    [(⊕ (⊘ u w) (⊘ v w))  (together expr)]
    [(⊕ u v)              (let ([cv (c v)])
                            (cond [(equal? v cv)    (⊕ u cv)]     ; Trival case
                                  [else          (c (⊕ u cv))]))] ; May match special cases after inner combination.
    [_ expr]))

(module+ test
  (displayln "TEST - combine")
  (check-equal? (combine (⊕ (⊘ (⊕ x) z) (⊘ (⊕ y x) z) (⊘ 1 z)))
                '(* (expt z -1) (+ 1 (* 2 x) y)))
  (check-equal? (combine (⊕ (⊘ (⊕ x) 3) (⊘ (⊕ y x) 3) (⊘ 1 3)))
                '(* 1/3 (+ 1 (* 2 x) y))))

(define (together-denominator s) (denominator (together s)))
(define (together-numerator   s) (numerator   (together s)))

(define-match-expander QuotientTogether
  ; Note: This matches everything and writes it as a quotient.
  (λ (stx) (syntax-parse stx [(_ u v) #'(and (app together-numerator u) (app together-denominator v))])))


; test cases adapted from https://reference.wolfram.com/language/ref/Numerator.html?view=all
(module+ test
  (real-mode) 
  (check-equal? (together-denominator 2/3) 3)  
  (check-equal? (together-denominator (⊘ (⊗ (⊖ x 1) (⊖ x 2))
                                         (Sqr (⊖ x 3))))
                (Sqr (⊖ x 3)))
  (check-equal? (together-denominator (⊕ 3/7 (⊗ 1/11 @i))) 77)
  (check-equal? (together-denominator (⊘ (Sqr (⊖ x 1))
                                         (⊗ (⊖ x 2) (⊖ x 3))))
                (⊗ (⊖ x 2) (⊖ x 3)))
  ; not consistent with mma, e^(a-b) 's together-denominator is 1, mma will return e^b, i.e. negative exponent powers.
  ; (check-equal? (together-denominator (⊗ 'a (Expt 'x 'n) (Expt 'y (⊖ 'm)) (Exp (⊕ 'a (⊖ 'b) (⊗ -2 'c) (⊗ 3 'd)))))
  ;               '(* (expt @e (* -1 (+ (* -1 b) (* -2 c)))) (expt y m))) ; should be simplified.
  (check-equal? (together-denominator (⊘ (Expt 'a (⊖ 'b)) x)) '(* (expt a b) x))
  (check-equal? (together-denominator (⊗ 2 (Expt x y) (Expt 'b 2))) 1))

; used for quotient.
; first call together, then split up the term-numerator/denominator parts.
; differences can be indicated by the following tests.
(define (mma-numerator/denominator s)
  (term-numerator/denominator (together s)))


(module+ test
  (displayln "TEST - term-numerator/denominator")
  (let-values ([(n d) (mma-numerator/denominator (normalize '(+ (/ x y) 2/3)))])
    (check-equal? n '(+ (* 3 x) (* 2 y)))
    (check-equal? d '(* 3 y)))
  ; test cases adapted from https://reference.wolfram.com/language/ref/NumeratorDenominator.html?view=all
  (let-values ([(n d) (mma-numerator/denominator (⊕ 3/7 (⊗ 1/11 @i)))])
    (check-equal? n '(+ (* @i 7) 33))
    (check-equal? d 77))
  ; Is this test case correct?
  #;(let-values ([(n d) (mma-numerator/denominator 
                         (⊗ 'a (Expt 'x 'n) (Expt 'y (⊖ 'm)) (Exp (⊕ 'a (⊖ 'b) (⊗ -2 'c) (⊗ 3 'd)))))])
      (check-equal? n '(* (expt @e (+ a (* 3 d))) a (expt x n)))
      (check-equal? d '(* (expt @e (* -1 (+ (* -1 b) (* -2 c)))) (expt y m))) ; better to simplify (* -1 (+ (* -1 b) (* -2 c))))
      ))
