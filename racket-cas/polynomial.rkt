#lang racket/base
;;; A GME (General Monomial Expression has the form:
;;;      c1 c2 ... cr x1^n1 x2^n2 ... xm^nm
;;; where (free-of ci xj) holds and nj are non-negative integers.

;;; A GPE (General Polynomial Expressions) is either
;;; a GME or a sum of GMEs.

(provide exponent             ; (exponent u w)               finds the maximum exponent of w present in u
         coefficient          ; (coefficient u v [n 1])      find coefficient of v^n in u
         polynomial?          ; (polynomial? u x)            is u a univariate polynomial in x?
         coefficient-list     ; (coefficient-list u x)       view u as a polynomial in x, return the list of coefficients
         is-power-of?         ; (is-power-of? u w)           view u as a power of w, is it a non-zero exponent?
         leading-coefficient  ; (leading-coefficient u x)    view u as a polynomial in x, return leading coefficient
         leading-term         ; (leading-term u x)           view u as a polynomial in x, return leading term
         variables            ; (variables u)                return list of expressions in which u is a polynomial
         collect              ; (collect u x)                rewrite u as a polynomial in x
         polynomial-quotient  ; (polynomial-quotient u v x)  quotient  for u divided by v, where u and v are polymials in x
         polynomial-remainder ; (polynomial-remainder u v x) remainder for u divided by v, where u and v are polymials in x
         polynomial-quotient-remainder ;                     list of quotient and remainder
         polynomial-expansion
         polynomial-gcd
         polynomial-square-free?
         polynomial-square-free-factor
         )

;;;
;;; Polynomial
;;;


(require racket/math math/number-theory
         racket/function racket/match racket/set
         (except-in racket/list permutations)
         "core.rkt" "diff.rkt" "expand.rkt" "math-match.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require "normalize.rkt" 'normalize))
  (define x 'x) (define y 'y) (define z 'z))


(define (exponent u w)
  ; find the maximum exponent of w which is present in u
  (define (e u)
    (math-match u
      [0 -inf.0]
      [u #:when (equal? u w) 1]
      [r 0]
      [r. 0]
      [x 0]
      [(⊕ u v) (max (e u) (e v))]
      [(⊗ u v) (+ (e u) (e v))]
      [(Expt u r) #:when (equal? u w) r]
      [(Expt (⊕ u v) r) (* (max (e u) (e v)) r)]
      [_ 0]))
  (e u))

(module+ test
  (displayln "TEST - exponent")
  (check-equal? (exponent 0 x) -inf.0)
  (check-equal? (exponent x x) 1)
  (check-equal? (exponent (Expt x 2) x) 2)
  (check-equal? (exponent '(+ 1 x (expt x 2)) x) 2)
  (check-equal? (exponent '(+ 1 x (expt x 2)) y) 0)
  (check-equal? (exponent '(* 1 x (+ 1 (expt x 2))) x) 3)
  (check-equal? (exponent '(sin x) x) 0)
  (check-equal? (exponent '(expt (+ 1 x) 7) x) 7))


; (coefficient u v)   find coefficient of v in u
; (coefficient u v n) find coefficient of v^n in u
; (coeffecient u v 0) returns the sum of all terms not of the form c*v^n, n>0
(define (coefficient u v [n 1])
  (when debugging? (displayln (list 'coefficient u v 'n n)))
  (define (c u)
    (math-match u
      [r                            (if (= n 0) r    0)]
      [r.bf                         (if (= n 0) r.bf 0)]
      [u #:when (equal? u v)        (if (= n 1) 1 0)]
      [y #:when (not (equal? y v))  (if (= n 0) y 0)]
      [(⊗ r w)                      (⊗ r (c w))]
      [(⊗ u w) #:when (equal? u v)  (coefficient w v (- n 1))]
      [(⊗ u w) #:when (equal? w v)  (coefficient u v (- n 1))]
      [(⊗ u w)                      (for/⊕ ([i (in-range (+ n 1))])
                                           (⊗ (coefficient u v i) (coefficient w v (- n i))))]
      [(⊕ u w)                      (⊕ (c u) (c w))]
      [(Expt u r) #:when (equal? u v) (cond [(= r n)                                       1]
                                            [(= n 0) (if (and (integer? r) (positive? r)) 
                                                         0 (Expt u r))] ; xxx
                                            [else                                          0])]
      [(Expt (⊕ u w) m)             (for/⊕ ([i (in-range (+ m 1))])
                                           (⊗ (binomial m i)
                                              (coefficient (⊗ (Expt u i) (Expt w (- m i))) v n)))]
      [u                            (if (= n 0) u 0)]))
  (c u))

(module+ test 
  (displayln "TEST - coefficient")
  (let () (define u (normalize '(+ (* 3 (expt x 2) y z) x (* 2 (expt x 2)))))
    (check-equal? (coefficient u (Expt x 2)) '(+ 2 (* 3 y z)))
    (check-equal? (coefficient u x 2) '(+ 2 (* 3 y z)))
    (check-equal? (coefficient u x) 1)
    (check-equal? (coefficient '(expt (+ x 1) 2) x) 2)
    (check-equal? (coefficient '(* (expt a -1) x)  x) '(expt a -1))
    (check-equal? (coefficient (normalize '(+ 1 x (sqr x) (sin x))) x 0) '(+ 1 (sin x)))
    (check-equal? (coefficient (⊘ 3 x) x 1) 0)
    (check-equal? (coefficient (⊘ 3 x) x -1) 3)
    (check-equal? (coefficient (Sqrt x) x 0) (Sqrt x))))

; (polynomial? u x)  is u a univariate polynomial in x ?
(define (polynomial? u x)
  (free-of (coefficient u x 0) x))

(module+ test
  (displayln "TEST - polynomial?")
  (check-equal? (polynomial? '(/ z x) x) #f)
  (check-true 
   (andmap (curryr polynomial? x) 
           (list 0 x '(expt x 2) '(* 3 (expt x 4)) '(expt (+ 1 x) 3)
                 (⊕ (⊘ 3 y) (Expt x 2))))))



(define (coefficient-list u x)
  ; view u as a polynomial in x, return the list of coefficients
  ; use same interpretation as  coefficient  for terms not in the form c*x^n
  (define max-n (exact-floor (max 0 (exponent u x))))
  (match (for/list ([n (in-range (+ max-n 1))]) (coefficient u x n))
    [(list 0) '()] [cs cs]))

(module+ test 
  (displayln "TEST - coefficient-list")
  (check-equal? (coefficient-list 42 x) '(42))
  (check-equal? (coefficient-list 0 x) '())
  (check-equal? (coefficient-list 'x x) '(0 1))
  (check-equal? (coefficient-list '(expt x 3) x) '(0 0 0 1))
  (check-equal? (coefficient-list '(* a x) x) '(0 a))
  (check-equal? (coefficient-list (normalize '(+ (* a x) (* b y) (* c x))) x) '((* b y) (+ a c)))
  (check-equal? (coefficient-list '(+ x (* 2 a (expt x 3))) x) '(0 1 0 (* 2 a)))
  (check-equal? (coefficient-list (⊘ 'z 'x) x) (list (⊘ 'z 'x))))

(define (is-power-of? u w)
  ; view u as a power of w, is it a non-zero exponent?
  (not (zero? (exponent u w))))

(module+ test
  (displayln "TEST - is-power-of?")
  (check-equal? (is-power-of? '(expt x 3) x) #t)
  (check-equal? (is-power-of? '(expt y 3) x) #f)
  (check-equal? (is-power-of? '(sin x) x) #f))


(define (leading-coefficient u x)
  (coefficient u x (exponent u x)))

(module+ test
  (displayln "TEST - leading-coefficient")
  (check-equal? (leading-coefficient '(+ 2 (* 3 x) (* 17 x x)) x) 17))

(define (leading-term u x)
  (define n (exponent u x))
  (⊗ (coefficient u x n) (Expt x n)))

(module+ test
  (displayln "TEST - leading-term")
  (check-equal? (leading-term '(+ 2 (* 3 x) (* 17 x x)) x) (⊗ 17 x x)))

(define (variables u)
  ; return list of expressions in which u is a polynomial
  (define (vars u vs)
    (math-match u
      [r          vs]
      [r.bf       vs]
      [x          (set-add vs x)]
      [(⊗ u v)   (vars u (vars v vs))]
      [(⊕ u v)   (vars u (vars v vs))]
      [(Expt u α) (vars u vs)]
      [else       (set-add vs u)]))
  (sort (set->list (vars u (set))) <<))

(module+ test
  (displayln "TEST - variables")
  (check-equal? (variables '(+ (expt (+ x y) 3) z (* a b c) (sin u))) '(a b c x y z (sin u))))


(define (collect u x)
  ; rewrite u as a polynomial in x
  (for/⊕ ([n (in-naturals)]
          [c (in-list (coefficient-list u x))])
         (⊗ c (Expt x n))))

(module+ test
  (check-equal? (collect '(+ (* x y) x -3 (* 2 x x) (* -1 z x x) (* x x x)) x)
                (⊕ -3 (⊗ x (⊕ 1 y)) (⊗ (Expt x 2) (⊕ 2 (⊗ -1 z))) (Expt x 3))))


;;; A GME (General Monomial Expression has the form:
;;;      c1 c2 ... cr x1^n1 x2^n2 ... xm^nm
;;; where (free-of ci xj) holds and nj are non-negative integers.

;;; A GPE (General Polynomial Expressions) is either
;;; a GME or a sum of GMEs.

(define (polynomial-quotient-remainder u v x)
  ; u and v are polynomials in one variable x.
  ; return list if quotient and remainder
  ; Algorithm is correct, but think about efficiency.
  (define (lc u) (leading-coefficient u x))
  (let ([u (collect u x)] [v (collect v x)])
    ; (displayln (list 'u u 'v 'v))
    (define lcv (lc v))
    (define n (exponent v x))
    ; invariant: u = q*v + r,  m=degree(r)
    (let loop ([q 0] [r u] [m (exponent u x)])
      ; (displayln (list 'q q 'r r 'm m))
      (cond
        [(>= m n) (define lcr (lc r))
                  (define t (⊗ (⊘ lcr lcv) (Expt x (- m n))))
                  (define r+ (expand (⊖    (⊖ r (⊗ lcr (Expt x m)))
                                           (⊗ (⊖ v (⊗ lcv (Expt x n))) t))))
                  (loop (⊕ q t) r+ (exponent r+ x))]
        [else     (list (distribute q) (distribute r))]))))

(define (polynomial-quotient u v x)
  (first (polynomial-quotient-remainder u v x)))

(define (polynomial-remainder u v x)
  (second (polynomial-quotient-remainder u v x)))

(module+ test
  (displayln "TEST - polynomial-quotient and friends")
  (let ([a 'a] [b 'b]) 
    (check-equal? (polynomial-quotient (Sqr x) (⊕ x a) x) (⊕ (⊖ a) x))
    (check-equal? (polynomial-quotient-remainder '(+ (* x x) x 1) '(+ (* 2 x) 1) x)
                  (list (⊕ 1/4 (⊘ x 2)) 3/4))
    (check-equal? (polynomial-quotient (⊕ (⊗ x x) (⊗ b x) 1) (⊕ (⊗ a x) 1) x)
                  '(+ (* -1 (expt a -2)) (* (expt a -1) b) (* (expt a -1) x))))

  ; The following tests are commented out due to loops.
  ; I think the cause is expand-all.
  #;(check-equal? (polynomial-quotient-remainder (normalize '(+ (* 2+4i x x) (* -1-8i x) -3+3i))
                                               (normalize '(+ (* 1+2i x) 1-i))
                                               x)
                '((+ -3 (* 2 x)) 0))
  #;(check-equal? (polynomial-quotient-remainder (normalize '(+ (* 2+4i x x) (* -1-8i x) -3+3i))
                                               (normalize '(+ (* 1+2i x) 1-i))
                                               x)
                '((+ -3 (* 2 x)) 0)))

(define (polynomial-expansion u v x t)
  ; u GPE in x, v GPE in x with deg(v,x)>0, x and t symbols
  (match u
    [0 0]
    [_ (match-define (list q r) (polynomial-quotient-remainder u v x))
       (expand (⊕ (⊗ t (polynomial-expansion q v x t)) r))]))

(module+ test 
  (let ([u (⊕ (⊗ x x x x x) (⊗ 11 x x x x) (⊗ 51 x x x) (⊗ 124 x x) (⊗ 159 x) 86)]
        [v (⊕                                            (⊗     x x) (⊗   4 x)  5)])
    (check-equal? (coefficient-list (polynomial-expansion u v x 't) 't)
                  '((+ 1 x) (+ 2 x) (+ 3 x)))))

(define (polynomial-gcd u v x)
  ; u and v are polynomials in F[x]
  ; where automatic simplification handles operations in F
  (when debugging? (displayln (list 'polynomial-gcd u v x)))
  (define U
    (match* (u v)
      [(0 0) 0]
      [(_ _) (let loop ([U u] [V v])
               (match V
                 [0 U]
                 [_ (loop V (polynomial-remainder U V x))]))]))
  (expand (⊗ (⊘ 1 (leading-coefficient U x)) U)))

(module+ test (check-equal? (polynomial-gcd '(* (expt (+ 1 x) 2) (+ 2 x) (+ 4 x))
                                            '(* (+ 1 x) (+ 2 x) (+ 3 x)) x)
                            '(+ 2 (* 3 x) (expt x 2))))

(define (polynomial-square-free? u x)
  ; u a univariate polynomial in the symbol x
  ; is u square-free ?
  (equal? (polynomial-gcd u (diff u x) x) 1))

(module+ test
  (displayln "TEST - polynomial-square-free?")
  (let ([u (⊕ x 1)] [v (⊕ x 2)] [w (⊕ x -1)])
    (check-equal? (andmap (curryr polynomial-square-free? x) (list u v w)) #t)
    (check-equal? (polynomial-square-free? (⊗ u v) x) #t)
    (check-equal? (polynomial-square-free? (⊗ u w) x) #t)
    (check-equal? (polynomial-square-free? (⊗ v w) x) #t)
    (check-equal? (polynomial-square-free? (⊗ u u v w) x) #f)
    (check-equal? (polynomial-square-free? (⊗ u v v w) x) #f)
    (check-equal? (polynomial-square-free? (⊗ u w v w) x) #f)))

(define (polynomial-square-free-factor u x)
  ; u is a univariate polynomial in x
  ; factor u = f*s^2 where f is square free
  (match u
    [0 u]
    [_ (define c (leading-coefficient u x))
       (define U (expand (⊘ u c)))
       (define R (polynomial-gcd U (diff U x) x))
       (define F (polynomial-quotient U R x))
       (let loop ([j 1] [P 1] [R R] [F F])
         (match R
           [1 (⊗ c P (Expt F j))]
           [_ (define G (polynomial-gcd R F x))
              (define P+ (⊗ P (Expt (polynomial-quotient F G x) j)))
              (define R+ (polynomial-quotient R G x))
              (define F+ G)
              (loop (+ j 1) P+ R+ F+)]))]))

(module+ test
  (displayln "TEST - polynomial-square-free-factor")
  (check-equal? 
   (polynomial-square-free-factor (expand '(* (+ x -1) (expt (+ x 1) 2) (expt (+ x 2) 5))) x)
   (⊗ (Expt (⊕ 1 x) 2) (Expt (⊕ 2 x) 5) (⊕ -1 x)))
  (let ([u (⊕ (⊗ x x x x x) (⊗ 6 x x x x) (⊗ 10 x x x) (⊗ -4 x x) (⊗ -24 x) -16)])
    (check-equal? (polynomial-square-free-factor u x) '(* (expt (+ 2 x) 3) (+ -2 (expt x 2))))))
