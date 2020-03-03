#lang racket/base
(provide solve  ; (solve eqn x)  solve equation wrt a variable x
         roots) ; (roots u x)    find solutions to u=0 
;;;
;;; Equation Solver
;;;


(require racket/list racket/match
         "core.rkt" "math-match.rkt"
         (prefix-in % "bfracket.rkt"))

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x)
  (define y 'y)
  (define z 'z))



(define (solve eqn x) ; assume x is real (use csolve for complex solutions)
  (when debugging? (displayln (list 'solve eqn x)))
  (let/ec return
    (define (solve-by-inverse w)
      (when debugging? (displayln (list 'solve-by-inverse w)))
      (define (remove-invertibles w)
        (when debugging? (displayln (list 'remove-invertibles w)))
        ; Input:  w = (Equal u v) where v is free of x
        ; Output: If w=f(u) then (remove-invertibles u (f^-1 v))
        ;         otherwise w.
        (define r remove-invertibles)
        (math-match w
          [(Equal (⊕ w u) v)     #:when (free-of w x) (r (Equal u (⊖ v w)))]
          [(Equal (⊕ u w) v)     #:when (free-of w x) (r (Equal u (⊖ v w)))]
          [(Equal (⊗ w u) v)     #:when (free-of w x) (r (Equal u (⊘ v w)))]
          [(Equal (⊗ u w) v)     #:when (free-of w x) (r (Equal u (⊘ v w)))]
          [(Equal (Ln v) w)      #:when (free-of w x)
                                 (r (Equal v (Exp w)))]
          [(Equal (Log v) w)      #:when (free-of w x)
                                 (r (Equal v (Expt 10 w)))]
          [(Equal (Log u v) w)   #:when (free-of w x)
                                 (r (Equal v (Expt u w)))]
          [(Equal (Expt @e u) s) #:when (> s 0)        (r (Equal u (Ln s)))]
          [(Equal (Expt @e u) s) (return #f)]
          [(Equal (Expt @e u) v) (r (Equal u (Ln v)))]  ; xxx TODO message: only correct if v>0 
          [(Equal (Expt u n) v)  #:when (odd? n)   (r (Equal u (Expt v (⊘ 1 n))))]
          [(Equal (Expt u n) α)  #:when (and (even? n) (< α 0)) #f]
          [(Equal (Expt u n) α)  #:when (and (even? n) (= α 0))
                                 (cond [(> n 0) (r (Equal u 0))]
                                       [(< n 0) #f]
                                       [(= n 0) #f])] ; NSpire signals warning due to 0^0
          [(Equal (Expt u n) α)  #:when (and (even? n) (> n 2) (> α 0))
                                 (let ([n/2 (/ n 2)] [sqrt-α (Sqrt α)] [u^n/2 (Expt u (/ n 2))])
                                   (cond [(even? n/2)      (solve (Equal u^n/2    sqrt-α) x)]
                                         [else (return (Or (solve (Equal u^n/2 (⊖ sqrt-α)) x)
                                                           (solve (Equal u^n/2    sqrt-α)  x)))]))]
          [(Equal (Expt u n) v)  #:when (and (even? n) (> n 2))
                                 (let ([n/2 (/ n 2)] [sqrt-v (Sqrt v)] [u^n/2 (Expt u (/ n 2))])
                                   (cond [(even? n/2)      (solve (Equal u^n/2    sqrt-v) x)]
                                         [else (return (Or (solve (Equal u^n/2 (⊖ sqrt-v)) x)
                                                           (solve (Equal u^n/2    sqrt-v)  x)))]))]
          [(Equal (Expt u -1) v) (r (Equal u (Expt v -1)))] ; assumes v<>0 (as does MMA)
          [(Equal (Expt u 1/2) v)     (solve (Equal u (Expt v 2))  x)] ; XXX 
          [(Equal (Expt u α) v)  #:when (= (%numerator α) 1) (r (Equal u (Expt v (⊘ 1 α))))]
          [(Equal (Expt n u) m)  #:when (and (free-of n x) (free-of m x)) (r (Equal u (Log n m)))]
          [(Equal (Expt v u) w)  #:when (and (free-of v x) (free-of w x)) (r (Equal u (Log v w)))]          
          [(Equal (Asin u) v) (r (Equal u (Sin v)))]
          [(Equal (Acos u) v) (r (Equal u (Cos v)))]
          [(Equal (Cos u) s)  #:when (or (> s 1) (< s -1)) (return #f)]
          [(Equal (Cos u) v)  (return (Or (solve (Equal u (⊕ (⊗ 2 @pi '@n)    (Acos v)))  x)
                                          (solve (Equal u (⊕ (⊗ 2 @pi '@n) (⊖ (Acos v)))) x)))]
          [(Equal (Sin u) s)  #:when (or (> s 1) (< s -1)) (return #f)]
          [(Equal (Sin u) v)  (return (Or (solve (Equal u (⊕ (⊗ 2 @pi '@n) (⊖ @pi (Asin v)))) x) 
                                          (solve (Equal u (⊕ (⊗ 2 @pi '@n)        (Asin v)))  x)))]
          [_ w]))
      
      (match (match (N w) [#t #t] [#f #f] [_ w])
        [(Equal u v) ; got an equation
         (cond      
           [(free-of v x) (remove-invertibles (Equal u v))]
           [(free-of u x) (remove-invertibles (Equal v u))]
           [else          w])]
        [w w]))
    (define (solve1 eqn) ; where eqn is returned from solve-by-inverse
      (when debugging? (displayln (list 'solve1 eqn)))
      (match eqn
        ; rewrite u=v to u-v=0
        [(Equal u v) #:when (not (equal? v 0)) (solve1 (Equal (⊖ u v) 0))]
        ; rule of zero product
        [(Equal (⊗ u v) 0)    (Or (solve (Equal u 0) x) (solve1 (Equal v 0)))]
        [(Equal (Expt u r) 0) (solve1 (Equal u 0))]
        [(Equal (⊕ u0 (Piecewise us vs)) 0)
         (logical-expand (apply Or: (for/list ([u us] [v vs])
                                      (define s (solve1 (Equal u (⊖ u0))))
                                      (And s v))))]
        [(Equal u 0) 
         (match (coefficient-list u x) ; note: leading coef is non-zero
           [(list)       #t]
           [(list a)     (Equal a 0)]            ; zero order
           [(list b a)   (Equal x (⊘ (⊖ b) a))]  ; first order
           ; second order
           [(list 0 0 a) (Equal x 0)]
           [(list 0 b a) (Or (Equal x 0) (Equal x (⊖ (⊘ b a))))]
           [(list c 0 a) (Or (Equal x (⊖ (Sqrt (⊘ (⊖ c) a))))
                             (Equal x    (Sqrt (⊘ (⊖ c) a))))]
           [(list c b a) (define d (⊖ (Sqr b) (⊗ 4 a c)))
                         (math-match d 
                           [0 (⊘ (⊖ b) (⊗ 2 a))]
                           [r #:when (negative? r) #f] ; no solutions
                           [_ (define sqrt-d (Sqrt d))
                              ; Note: If d is symbolic, we can't know the sign
                              ;       We assume we are in the positive case
                              (Or (Equal x (distribute (⊘ (⊖ (⊖ b) sqrt-d) (⊗ 2 a))))
                                  (Equal x (distribute (⊘ (⊕ (⊖ b) sqrt-d) (⊗ 2 a)))))])]
           ; try factoring
           [_ (match (polynomial-square-free-factor u x)
                ; it helped!
                [(⊗ v w) (solve1 (Equal (⊗ v w) 0) x)]
                ; give up
                [_        (Equal u 0)])]
           [_ (Equal u 0)])]
        [w w]))
    (solve1 (solve-by-inverse eqn))))

(module+ test
  (check-equal? (solve '(= x 1) x) '(= x 1))
  (check-equal? (solve '(= 1 x) x) '(= x 1))
  (check-equal? (solve '(= x y) x) '(= x y))
  (check-equal? (solve '(= y x) x) '(= x y))
  (check-equal? (solve '(= 1 1) x) #t)
  (check-equal? (solve '(= 1 2) x) #f)
  (check-equal? (solve '(= x x) x) #t)
  (check-equal? (solve '(= (+ x 1) (+ x 1)) x) #t)
  (check-equal? (solve '(= (* 3 x) 2) x) '(= x 2/3))
  (check-equal? (solve (normalize '(= (sqr x) 9)) x) '(or (= x -3) (= x 3)))
  (check-equal? (solve '(= (asin x) 1/2) x) '(= x (sin 1/2)))
  (check-equal? (solve '(= (acos x) 1/2) x) '(= x (cos 1/2)))
  (check-equal? (solve '(= (* 3 x) 2) x) '(= x 2/3))
  (check-equal? (solve (normalize '(= (* (- x 1) (- x 2) (- x 3)) 0)) x) 
                '(or (= x 1) (= x 2) (= x 3)))
  (check-equal? (solve (normalize '(= 8.0 (expt 2.0 x))) x) '(= x 3.0))
  (check-equal? (solve '(= 8 (expt 2 x)) x) '(= x 3))
  (check-equal? (solve (normalize '(= (- (- x) 6) 0)) 'x) '(= x -6))
  (check-equal? (solve '(= (log x 2) 2) 'x) '(or (= x (* -1 (expt 2 1/2))) (= x (expt 2 1/2))))
  (check-equal? (solve '(= (log 5 x) 2) 'x) '(= x 25))
  (check-equal? (solve '(= (log x) 2) 'x) '(= x 100))
  (check-equal? (solve '(= (ln x) 2) 'x) '(= x (expt @e 2)))
  (check-equal? (solve '(= (sin x) 1) x) '(= x (+ (* 2 @n @pi) (* 1/2 @pi)))))


(define (roots u x)
  (define (solution u) (last u))
  (define (extract u)
    (match u
      [(list 'or e ...) (map solution e)]
      [(list '= y x0) #:when (equal? y x)
                      (list x0)]
      [_                '()]))
  (extract (solve (Equal u 0) x)))


(module+ test
  (check-equal? (roots '(+ (expt x 2) -1) x) '(-1 1)))

; > (let () ; Example: The discriminant of a second degree polynomial
;     (match-define (list x1 x2) (roots '(+ (* x x) (* b x) c) x))
;     (expand (Sqr (⊖ x1 x2))))
; '(+ (expt b 2) (* -4 c))

