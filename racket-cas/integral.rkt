#lang racket/base
(provide integrate)

;;;
;;; NOTES ON ADDING PR11 THE REFACTOR BRANCH
;;;

; 1. This line wasn't added to Oslash:
;       [((TimesTerms (== v) us ...) _) (apply ⊗ us)]
;    The problem is that it is expensive - and thus is not suited for automatic simplification.
;    Maybe it can be added to cancel instead?

; 2. Problem with match pattern p-, p+ (and similar).

; 3. A few test cases now fail that didn't before. Maybe due to 1, but maybe due
;    to the refactoring.


;;;
;;; Integral
;;;

(require racket/list racket/match racket/format
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "runtime-paths.rkt"
         "polynomial.rkt" "logical-operators.rkt"  "relational-operators.rkt" "trig.rkt"
         "compose-app.rkt" "solve.rkt" "diff.rkt" )

(define normalize (dynamic-require normalize.rkt       'normalize))
(define subst     (dynamic-require simplify-expand.rkt 'subst))
(define expand    (dynamic-require expand.rkt          'expand))

(module+ test
  (require rackunit math/bigfloat)
  (define N (dynamic-require numerical-evaluation.rkt 'N))
  (define x 'x) (define y 'y) (define z 'z))



;;; The pattern (Sum us) matches a sum of the form (+ u ...) and binds us to (list u ...)
(define-match-expander Sum
  (λ (stx) (syntax-case stx () [(_ us) #'(list* '+ us)])))
;;; The pattern (Prod us) matches a product of the form (* u ...) and binds us to (list u ...)
(define-match-expander Prod
  (λ (stx) (syntax-case stx () [(_ us) #'(list* '* us)])))


(module+ test
  (displayln "TEST - Matcher: Prod")
  (check-equal? (match '(*)       [(Prod us) us]) '())
  (check-equal? (match '(* x)     [(Prod us) us]) '(x))
  (check-equal? (match '(* x y)   [(Prod us) us]) '(x y))
  (check-equal? (match '(* x y)   [(Prod (list (== x) b)) b]) 'y)
  (check-equal? (match '(* x y z) [(Prod (list-no-order (== y) b ...)) b]) '(x z)))

;;; The pattern (PlusTerms pt ...) matches a product of the form (+ u ...) and binds (list pt ...) to (list u ...);
;;; Length of (list pt ...) and (list u ...) must equal.
;;; Mapping from (list u ...) to (list pt ...) can be out of order as needed.
(define-match-expander PlusTerms
  (λ (stx) (syntax-case stx () [(_ u ...) #'(cons '+ (list-no-order u ...))])))

(module+ test
  (displayln "TEST - Matcher: PlusTerms")
  (check-equal? (match '(+ x y z) [(PlusTerms 'z b c) (list b c)]) '(x y))
  (check-equal? (match '(+ x y z) [(PlusTerms 'z b ...) b]) '(x y))
  (check-equal? (match '(+ (cos x) (sin y)) [(PlusTerms (Sin a) b) (list a b)]) '(y (cos x))))

;;; The pattern (TimesTerms tt ...) matches a product of the form (* u ...) and binds (list tt ...) to (list u ...);
;;; Length of (list pt ...) and (list u ...) must equal.
;;; Mapping from (list u ...) to (list tt ...) can be out of order as needed.
(define-match-expander TimesTerms
  (λ (stx) (syntax-case stx () [(_ u ...) #'(cons '* (list-no-order u ...))])))

(module+ test
  (displayln "TEST - Matcher: TimesTerms")
  (check-equal? (match '(* x y z) [(TimesTerms 'z b c) (list b c)]) '(x y))
  (check-equal? (match '(* (cos x) (sin y)) [(TimesTerms (Sin a) b) (list a b)]) '(y (cos x))))



(define (cancel w)
  (when debugging? (displayln (list 'cancel w)))
  (match w
    [(⊘ u v) (⊘ u v)]
    [_ w]))

(module+ test
  (displayln "TEST - cancel")
  (check-equal? (normalize '(* (expt (+ 1 x) -1) (cos x) (+ 1 x))) '(* (expt (+ 1 x) -1) (cos x) (+ 1 x)))
  (check-equal? (cancel '(* (expt (+ 1 x) -1) (cos x) (+ 1 x))) '(cos x)))

; Temp hard-coded reduce patterns for integrate.
; Should be replaced by more general rules.
(define (reduce expr)
  (when debugging? (displayln (list 'reduce expr)))
  (match expr
    [(TimesTerms u (PlusTerms (Expt v -1) vs ...) us ...)
     #:when (equal? u v)
     (reduce (⊗ (⊕ 1 (⊗ u (apply ⊕ vs))) (apply ⊗ us)))]
    [(TimesTerms (Expt u -1) (PlusTerms v vs ...) us ...)
     #:when (equal? u v)
     (reduce (⊗ (⊕ 1 (⊘ (apply ⊕ vs) v)) (apply ⊗ us)))]
    [(TimesTerms (Expt u1 v1) (Expt u2 v2) ws ...)
     #:when (equal? v1 v2)
     (define orig (⊗ u1 u2))
     (define reduced (reduce orig))
     (cond
       [(equal? reduced orig) (⊗ (reduce (Expt u1 v1)) (reduce (Expt u2 v2)) (reduce (apply ⊗ ws)))]
       [else (reduce (⊗ (Expt reduced v1) (apply ⊗ ws)))])]
    [(TimesTerms (Expt u1 (⊖ v)) (Expt u2 u) ws ...)
     #:when (equal? v u)
     (define orig (⊗ (⊘ 1 u1) u2))
     (define reduced (reduce orig))
     (cond
       [(equal? reduced orig) (⊗ (reduce (Expt u1 (⊖ v))) (reduce (Expt u2 u)) (reduce (apply ⊗ ws)))]
       [else (reduce (⊗ (Expt reduced v) (apply ⊗ ws)))])]
    [(TimesTerms (Expt u1 u) (Expt u2 (⊖ v)) ws ...)
     #:when (equal? v u)
     (define orig (⊗ (⊘ 1 u2) u1))
     (define reduced (reduce orig))
     (cond
       [(equal? reduced orig) (⊗ (reduce (Expt u1 u)) (reduce (Expt u2 (⊖ v))) (reduce (apply ⊗ ws)))]
       [else (reduce (⊗ (Expt reduced v) (apply ⊗ ws)))])]
    [(⊖ 1 (Sqr (Cos x))) ; trig
     (Sqr (Sin x))]
    [(⊖ 1 (Sqr (Sin x)))
     (Sqr (Cos x))]
    [(⊖ (Sqr (Cos x)) 1) ; trig
     (⊖ (Sqr (Sin x)))]
    [(⊖ (Sqr (Sin x)) 1)
     (⊖ (Sqr (Cos x)))]
    [(PlusTerms u (TimesTerms (Sqr (Cos x)) v ...))
     #:when (equal? (⊕ u (apply ⊗ v)) 0)
     (⊗ u (Sqr (Sin x)))]
    [(PlusTerms u (TimesTerms (Sqr (Sin x)) v ...))
     #:when (equal? (⊕ u (apply ⊗ v)) 0)
     (⊗ u (Sqr (Cos x)))]
    [(⊕ 1 (⊘ (Sqr (Sin t)) (Sqr (Cos t)))) (⊘ 1 (Sqr (Cos t)))]
    [(⊖ 1 (⊘ u (⊕ 1 u))) (⊘ 1 (⊕ 1 u))] ; for (diff (Atan x) x) and (integrate (diff (Atan x) x) x)
    [(app: f us)      (normalize (cons f (map reduce us)))]
    [_ expr]))

(module+ test
  (displayln "TEST - reduce")
  (check-equal? (reduce (⊗ (Sqr x) (Expt (⊕ (⊘ 1 x) y) 2))) '(expt (+ 1 (* x y)) 2))
  (check-equal? (reduce (⊗ (Sqr x) (Expt (⊕ (⊘ 1 x) y) 2) z)) '(* z (expt (+ 1 (* x y)) 2)))
  (check-equal? (reduce (⊗ (Expt y 2) (Expt (⊕ (⊘ 1 x) y) 2))) '(* (expt y 2) (expt (+ (expt x -1) y) 2)))
  (check-equal? (reduce '(* -1/2 (expt x -1) (expt (+ 2 (expt x -1) x) -1))) '(* -1/2 (expt (+ 1 (* x (+ 2 x))) -1)))
  (check-equal? (reduce '(* x (+ 2 (expt x -1) x))) '(+ 1 (* x (+ 2 x))))
  (check-equal? (reduce '(+ -1 (expt (cos x) 2) )) '(* -1 (expt (sin x) 2)))
  (check-equal? (reduce '(expt (+ 1 (* (expt (cos g) -2) (expt (sin g) 2))) 1/2)) '(expt (cos g) -1))
  (check-equal? (reduce '(* (expt (cos x) -2) (expt (sin x) 2) (expt (+ 1 (* (expt (cos x) -2) (expt (sin x) 2))) -1)))
                '(expt (sin x) 2))
  )


; Also match u as (Expt u 1).
; Will not match (Expt u 0).
(define-match-expander GreedyExpt
  (λ (stx) (syntax-parse stx [(_ u v) #'(or (Expt u v) (and u (bind: v 1)))])))

(module+ test
  (displayln "TEST - GreedyExpt")
  (check-equal? (match 2 [(GreedyExpt u v) (list u v)]) '(2 1))
  (check-equal? (match (Exp 'a) [(GreedyExpt u v) (list u v)]) '(@e a)))


(define (ax2+bx+c: x a b c)
  (⊕ (⊗ a (Sqr x))(⊕ (⊗ b x) c)))

(define (match-polynomials u x n)
  (when debugging? (displayln (list 'match-polynomials u n)))
  (define empty-result (make-list n 0))
    (cond
      [(not (= n (exponent u x)))
       empty-result]
      [else
         (define coeffs
           (for/list [(i (in-range n -1 -1))]
             (coefficient u x i)))
         (if (andmap (lambda (u) (free-of u x)) coeffs)
              coeffs
              empty-result)]))

(define (match-ax2+bx+c u x)
  (match-polynomials u x 2))

;;; Note: x is an input param (assigning variable of the polynomial) for the expander, not a pattern variable that accepts bindings.
(define-match-expander ax2+bx+c
  ; a!=0, b c can be 0.
  (λ (stx) (syntax-parse stx [(_ x a b c) #'(app (λ(u) (match-ax2+bx+c u x)) (list (? not-zero? a) b c))]))
  (λ (stx) (syntax-parse stx [(_ x a b c) #'(ax2+bx+c: x a b c)] [_ (identifier? stx) #'ax2+bx+c:])))

(module+ test
  (displayln "TEST - ax2+bx+c")
  (check-equal? (match '(expt z 2) [(ax2+bx+c z a b c) (list a b c)][_ #f]) '(1 0 0))
  (check-equal? (match '(expt y 2) [(ax2+bx+c z a b c) (list a b c)][_ #f]) #f)
  (check-equal? (match '(expt z 3) [(ax2+bx+c z a b c) (list a b c)][_ #f]) #f)
  (check-equal? (match '(+ z 2) [(ax2+bx+c z a b c) (list a b c)][_ #f]) #f)
  (check-equal? (match '(+ (expt z 2) z a) [(ax2+bx+c z a b c) (list a b c)][_ #f]) '(1 1 a)))

(define (rx+s: x r s)
  (⊕ (⊗ r x) s))

(define (match-rx+s u x)
  (match-polynomials u x 1))

(define-match-expander rx+s
  ; r!=0, s can be 0.
  (λ (stx) (syntax-parse stx [(_ x a b) #'(app (λ(u) (match-rx+s u x)) (list (? not-zero? a) b))]))
  (λ (stx) (syntax-parse stx [(_ x a b) #'(rx+s: x a b)] [_ (identifier? stx) #'rx+s:])))

(module+ test
  (displayln "TEST - rx+s")
  (check-equal? (match x              [(rx+s y r s) (list r s)][_ #f]) #f)
  (check-equal? (match y              [(rx+s y r s) (list r s)][_ #f]) '(1 0))
  (check-equal? (match '(+ (* x y) z) [(rx+s x r s) (list r s)][_ #f]) '(y z))
  (check-equal? (match '(+ (* x y) z) [(rx+s y r s) (list r s)][_ #f]) '(x z))
  (check-equal? (match '(+ (* x y) z) [(rx+s z r s) (list r s)][_ #f]) '(1 (* x y))))


; Find the subexpressions in u related to x. (not a sum, not x itself.)
; Util function for subst-candidates.
; The result is a super set of the final subst-candidates for integratal.
(define (extract-related-operands u x)
  (when debugging? (displayln (list 'extract-related-operands u x)))
  (define (non-free-of-x? u)
    (and (not (free-of u x)) (not (equal? u x))))
  (define (non-free-of-x-or-empty-list u)
    (if (non-free-of-x? u) `(,u) '()))
  (match u
    [(num: _) '()]
    [(var: _) '()]
    [(Sum us)  (filter non-free-of-x? us)]
    [(Prod us) (filter non-free-of-x? us)]
    ; find out implicit subst-rands, such as x^2 in x^4.
    [(Expt u n) #:when (and (not (free-of u x)) (integer? n) (or (>= n 4) (<= n -2)))
                (let ([common (list (Expt u (quotient n 2)) u)])
                  (if (< n 0)
                      (cons (Expt u (- n)) common)
                      common))]
    [(Expt u (⊖ v)) #:when (or (not (free-of u x)) (not (free-of v x)))
                    (list (Expt u v))]
    [(app: _ us) (filter non-free-of-x? us)]
    [_ (error "no case matched.")]))

(module+ test
  (displayln "TEST - extract-related-operands")
  (check-equal? (extract-related-operands (⊗ (Exp x) x)    x) '((expt @e x)))
  (check-equal? (extract-related-operands (⊗ (Expt x 5) x) x) '((expt x 3) x))
  (check-equal? (extract-related-operands (⊗ 3 (Sqr y))    y) '((expt y 2)))
  )

; Find the subexpressions in u that can be used in the "integration by substitution rule"
(define (subst-candidates u x)
  (define (x-subst-candidates u)
    (define new-ops (extract-related-operands u x))
    (if (empty? new-ops)
        '()
        (append new-ops
                (foldl append '()
                       (map x-subst-candidates new-ops))
                )))
  (remove-duplicates (x-subst-candidates u)))

(module+ test
  (displayln "TEST - subst-candidates")
  (check-equal? (subst-candidates (⊗ (Exp x) x) x) '((expt @e x)))
  (check-equal? (subst-candidates (⊗ (Exp (Sqr (Cos x))) x) x)
                '((expt @e (expt (cos x) 2)) (expt (cos x) 2) (cos x))))


(define (subst-with-symbol u x v [symbol 'symbol])
  (when debugging? (displayln (list 'subst-with-symbol u x v symbol)))
  (define (handle-multi-roots to-sub x0 roots [conditionals (list (Less x0 0) (GreaterEqual x0 0))])
    (define func-pieces (for/list ([root roots]) (subst to-sub x0 root)))
    (define first-func-piece (first func-pieces))
    (cond
      [(andmap (lambda (y) (equal? y first-func-piece)) func-pieces) first-func-piece]
      [else
       (Piecewise: func-pieces conditionals)]))
  (define (sub to-sub solution)
    (match solution
      [(list '= x0 s) #:when (and (free-of s x) (not (free-of x0 x)))
                      (subst to-sub x0 s)]
      [(list 'or (list '= x0 (⊖ s)) (list '= x0 s))
       #:when (and (free-of s x) (not (free-of x0 x)))
       (match s
         [(Acos _) (handle-multi-roots to-sub x0
                                       (list (⊖ s) s)
                                       (list (And (GreaterEqual x0 (⊗ -1/2 @pi)) (Less x0 0))
                                             (And (GreaterEqual x0 0) (Less x0 (⊗ 1/2 @pi)))))]
         [_ (handle-multi-roots to-sub x0 (list (⊖ s) s))])]
      [(list 'or (list '= x0 s) (list '= x0 (⊖ @pi s)))
       #:when (and (free-of s x) (not (free-of x0 x)))
       (handle-multi-roots to-sub x0
                           (list s (⊖ @pi s))
                           (list (And (GreaterEqual x0 0) (Less x0 (⊗ 1/2 @pi)))
                                 (And (GreaterEqual x0 (⊗ 1/2 @pi)) (Less x0 @pi))))]
      [_                to-sub]))
  (define solution (solve (Equal v symbol) x))
  (sub (subst u v symbol) (subst solution @n 0)))

(module+ test
  (displayln "TEST - subst-with-symbol")
  (check-equal? (subst-with-symbol (⊗ (Exp x) x) x '(expt @e x)) '(* symbol (ln symbol)))
  (check-equal? (subst-with-symbol (Expt x 4) x (Sqr x) 's) '(expt s 2))
  (check-equal? (subst-with-symbol '(* (expt x -1) (expt (expt x 2) 1/2)) x '(expt x 2) 'g) '(piecewise (-1 (< x 0)) (1 (>= x 0))))
  (check-equal? (subst-with-symbol (Cos x) x (Sin x) 's)
                '(piecewise       ((expt (+ 1 (* -1 (expt s 2))) 1/2) (and (< x (* 1/2 @pi)) (>= x 0)))
                            ((* -1 (expt (+ 1 (* -1 (expt s 2))) 1/2)) (and (< x @pi) (>= x (* 1/2 @pi))))))
  (check-equal? (subst-with-symbol (Sin x) x (Cos x) 's)
                '(piecewise ((* -1 (expt (+ 1 (* -1 (expt s 2))) 1/2)) (and (< x 0) (>= x (* -1/2 @pi))))
                                  ((expt (+ 1 (* -1 (expt s 2))) 1/2) (and (< x (* 1/2 @pi)) (>= x 0))))))

(define (integrate-table-failed? u)
  (equal? u 'integrate-table-failed))

(define (trig-subst u x parts)
  (parameterize [(real-mode? #t) (complex-mode? #f)]
    (define (free-of-x u) (free-of u x))
    (match parts
      [(Sqrt (⊖ a2 (Sqr (== x))))                       #:when (free-of-x a2)
                                                        (try-subst-integrate u x (Asin (⊘ x (Sqrt a2))))]
      
      [(Sqrt (⊖ (Sqr (== x)) a2))                       #:when (free-of-x a2)
                                                        (try-subst-integrate u x (Asec (⊘ x (Sqrt a2))))]
      
      [(Sqrt (⊕ a2 (Sqr (== x))))                       #:when (free-of-x a2)
                                                        (try-subst-integrate u x (Atan (⊘ x (Sqrt a2))))]
      
      [(Sqrt (⊖ a2 (TimesTerms (Sqr (== x)) b2 ...)))   #:when (andmap free-of-x (cons a2 b2))
                                                        (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                          (try-subst-integrate u x (Asin (⊗ x b/a))))]
      
      [(Sqrt (⊖ (TimesTerms (Sqr (== x)) b2 ...) a2))   #:when (andmap free-of-x (cons a2 b2))
                                                        (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                          (try-subst-integrate u x (Asec (⊗ x b/a))))]
      
      [(Sqrt (⊕ a2 (TimesTerms (Sqr (== x)) b2 ...)))   #:when (andmap free-of-x (cons a2 b2))
                                                        (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                          (try-subst-integrate u x (Atan (⊗ x b/a))))]
      
      [_ #f])))

;TODO TODO 
(module+ test
  (displayln "TEST - trig-subst")
  (check-equal? (trig-subst '(expt (+ 1 (expt x 2)) 1/2) x '(expt (+ 1 (expt x 2)) 1/2))
                (Atan x))
  (check-equal? (trig-subst '(expt (+ 1       (expt x 2)) -1/2) x '(expt (+ 1 (expt x 2)) 1/2))
                '(+ (* 1/2 x (expt (+ 1       (expt x 2)) -1/2)
                             (expt (+ 1 (* -1 (expt x 2) (expt (+ 1 (expt x 2)) -1))) 1/2))
                    (* 1/2 (asin (* x (expt (+ 1 (expt x 2)) -1/2)))))))


(define (try-subst-integrate u x v)
  (when debugging? (displayln (list 'try-subst-integrate u x v)))
  (define sym (gensym "t"))
  (define trival-integrand (⊘ u (diff v x)))
  (define (get-integrand-in-sym integrand-in-x subst-rand)
    (expand (reduce (cancel (subst-with-symbol integrand-in-x x v subst-rand)))))
  (define (get-integral-in-x integrand-in-sym sym-in-x)
    (subst (integrate-table integrand-in-sym sym) sym sym-in-x))
  (define (integ integrand-in-x subst-rand)
    (when debugging? (displayln (list 'integ integrand-in-x subst-rand)))
    (define sym-in-x v)
    (define integrand-in-sym (get-integrand-in-sym integrand-in-x subst-rand))
    (and (free-of integrand-in-sym x) (get-integral-in-x integrand-in-sym sym-in-x)))
  (cond
    [(integ trival-integrand sym)]
    [else (trig-subst u x v)
     ]))


(module+ test
  (displayln "TEST - try-subst-integrate")
  (check-equal? (try-subst-integrate (⊗ (Exp x) x) x '(expt @e x)) '(+ (* -1 (expt @e x)) (* (expt @e x) x)))
  (check-equal? (try-subst-integrate (Sqr (⊕ x 1)) x '(+ x 1)) '(* 1/3 (expt (+ 1 x) 3)))
  (check-equal? (try-subst-integrate (⊘ 1 (sqrt:1-x2 x)) x (sqrt:1-x2 x)) '(asin x))
  (check-equal? (try-subst-integrate (⊘ 1 (Sqrt (⊖ 'n (Sqr x)))) x (Sqrt (⊖ 'n (Sqr x))))
                '(* (expt n -1/2) (asin (* (expt n -1/2) x))))
  (check-equal? (try-subst-integrate (⊘ 1 (Sqrt (⊖ 'n (⊗ 'm (Sqr x))))) x (Sqrt (⊖ 'n (⊗ 'm (Sqr x)))))
                '(* (expt n -1/2) (asin (* (expt m 1/2) (expt n -1/2) x))))
  (check-equal? (try-subst-integrate (Sqrt (⊕ 1 (Sqr x))) x (Sqrt (⊕ 1 (Sqr x)))) (Atan x)) ; need reduce
  )

; Symbolic computation of
; 1, the indefinite integral of u wrt to x if a and b equal to #f.
; 2, the definite integral of u wrt to x with limits a and b.
; Only the basic cases have been implemented.
(define (integrate u x [a #f] [b #f])
  (when debugging? (displayln (list 'integrate u x a b)))
  (define (free-of-x u) (free-of u x))
  (define (integ u)
    (match u
      [(⊕ u v)   (⊕ (integ u) (integ v))]
      [(Prod us) #:when (ormap free-of-x us)
                 (define-values (free non-free) (partition free-of-x us))
                 (⊗ (apply ⊗ free) (integ (apply ⊗ non-free)))]
      [_ (or (integrate-impl u x) (raise 'integrate-fail))]))
  (with-handlers ([(lambda (u) (equal? u 'integrate-fail)) (lambda (u) #f)]) ; integrate-table-impl failed
    (define integral (integ u))
    (cond
      [(not (or a b)) integral]
      [(equal? a b) 0]
      [(and a b) (⊖ (subst integral x b) (subst integral x a))] ; todo, replace subst with more powerful limit function.
      [else (error 'integrate (~a "upper limit and lower limit should be provided at the same time" a b))]
      )))

; integrate common functions in integral table.
(define (integrate-table u x)
    (with-handlers ([integrate-table-failed? (lambda (u) #f)]) ; integrate-table-impl failed
      (integrate-table-impl u x)))

; integration by substitution rule
(define (integrate-subst u x)
  (when debugging? (displayln (list 'integrate-subst u x)))
  (define candidates (subst-candidates u x))
  (for/or ([c candidates])
    (try-subst-integrate u x c)
    ))

; try integrating each terms separately
(define (integrate-expand u x)
  (define expanded (expand u))
  (if
   (equal? expanded u)
   #f
   (integrate expanded x)))

; 1 try integrate-table (for functions in integral tables)
; 2 try integrate-subst (integration by substitution rule)
; 3 try integrate-expand, integrate each terms separately.
(define (integrate-impl u x)
  (when debugging? (displayln (list 'integrate-impl u x)))
  (cond
    [(integrate-table u x)  => values]
    [(integrate-subst u x)  => values]
    [(integrate-expand u x) => values]
    [else #f]))

(define (integrate-1/ax2+bx+c x a b c)
  (define b2-4ac (⊖ (Sqr b) (⊗ 4 a c)))
  (define 2ax+b (⊕ (⊗ 2 a x) b))
  (cond
    [(or (not (real? b2-4ac))
         (< b2-4ac 0)) (⊗ 2 (Atan (⊘ 2ax+b (Sqrt (⊖ b2-4ac)))) (Expt (⊖ b2-4ac) -1/2))]
    [(> b2-4ac 0) (⊗ -2 (Atanh (⊘ 2ax+b (Sqrt b2-4ac))) (Expt b2-4ac -1/2))]
    [(= b2-4ac 0) (⊘ -2 2ax+b)]))

(define (integrate-cos^n:x x n)
  (define (next-integ m)
    (integrate-cos^n:x x m))
  (cond
    [(> n 0)
     (define n-1 (- n 1))
     (define n-2 (- n 2))
     (⊕ (⊗ (/ n) (Expt (Cos x) n-1) (Sin x))
        (⊗ (/ n-1 n) (next-integ n-2)))]
    [(= n 0)  x]
    [(= n -1) (Ln (⊕ (Sec x) (Tan x)))]
    [(< n -1)
     (define n+1 (+ n 1))
     (define n+2 (+ n 2))
     (⊕ (⊗ (/ -1 n+1) (Expt (Cos x) n+1) (Sin x))
        (⊗ (/ n+2 n+1) (next-integ n+2)))]))

(define (integrate-sin^n:x x n)
  (define (next-integ m)
    (integrate-sin^n:x x m))
  (cond
    [(> n 0)
     (define n-1 (- n 1))
     (define n-2 (- n 2))
     (⊕ (⊗ (/ -1 n) (Expt (Sin x) n-1) (Cos x))
        (⊗ (/ n-1 n) (next-integ n-2)))]
    [(= n 0)  x]
    [(= n -1) (⊖ (Ln (⊕ (Csc x) (Cot x))))]
    [(< n -1)
     (define n+1 (+ n 1))
     (define n+2 (+ n 2))
     (⊕ (⊗ (/ -1 n+1) (Expt (Sin x) n+1) (Cos x))
        (⊗ (/ n+2 n+1) (next-integ n+2)))]))

; can compare abs(m) abs(n) to decide which term to reduce.
(define (integrate-sin^m:x.cos^n:x x m n)
  (define (next-integ m)
    (integrate-sin^m:x.cos^n:x x m n))
  (define n+1 (+ n 1))
  (define n+2 (+ n 2))
  (cond
    [(> m 0)
     (define m+n (+ m n))
     (cond
     [(= m+n 0)
      (if (even? m)
          (integrate (⊗ (Expt (⊖ 1 (Sqr (Cos x))) (/ m 2)) (Expt (Cos x) n)) x)
          (raise 'integrate-table-failed))] ; special case. ; subst cos^2:x as 1-sin^2:x for even m.
     [else
      (define m-1 (- m 1))
      (define m-2 (- m 2))
      (⊕ (⊗ (/ -1 m+n) (Expt (Sin x) m-1) (Expt (Cos x) n+1))
         (⊗ (/ m-1 m+n) (next-integ m-2)))])]
    [(= m 0) (integrate-cos^n:x x n)]
    [(= m -1) (raise 'integrate-table-failed)] ; need more work.
    [(< m -1)
     (define m+1 (+ m 1))
     (define m+2 (+ m 2))
     (define m+n+2 (+ m n 2))
     (⊕ (⊗ (/ 1 m+1) (Expt (Sin x) m+1) (Expt (Cos x) n+1))
        (⊗ (/ m+n+2 m+1) (next-integ n+2)))]))

;;; n can be any integers.
(define (integrate-x^n.e^ax+b x n a b)
  (define e^ax+b (Exp (⊕ (⊗ a x) b)))
  (define (next-integ m)
    (integrate-x^n.e^ax+b x m a b))
  (cond
    [(> n 0)  (⊕ (⊗ (⊘ 1 a) (Expt x n) e^ax+b) (⊗ (⊘ (- n) a) (next-integ (- n 1))))]
    [(= n 0)  (⊗ (⊘ 1 a) e^ax+b)]
    [(= n -1) (⊗ (⊖ 1 (⊘ 1 a)) (Ln x) e^ax+b)]
    [(< n -1)
     (define n+1 (+ n 1))
     (⊕ (⊗ (⊘ 1 n+1) (Expt x n+1) e^ax+b) (⊗ (⊘ (⊖ a) n+1) (next-integ n+1)))]))

;;; n can be any integers.
(define (integrate-x^n.sin:ax+b x n a b)
  (define sin:ax+b (Sin (⊕ (⊗ a x) b)))
  (define cos:ax+b (Cos (⊕ (⊗ a x) b)))
  (define (next-integ m)
    (integrate-x^n.cos:ax+b x m a b))
  (cond
    [(> n 0)  (⊕ (⊗ (⊘ -1 a) (Expt x n) cos:ax+b) (⊗ (⊘ n a) (next-integ (- n 1))))]
    [(= n 0)  (⊗ (⊘ -1 a) cos:ax+b)]
    [(= n -1) (⊕ (⊗ (Sin b) (Ci (⊗ a x))) (⊗ (Cos b) (Si (⊗ a x))))] ;;; special function, Ci, Si;
    [(< n -1)
     (define n+1 (+ n 1))
     (⊕ (⊗ (⊘ 1 n+1) (Expt x n+1) sin:ax+b) (⊗ (⊘ (⊖ a) n+1) (next-integ n+1)))]))

;;; n can be any integers.
(define (integrate-x^n.cos:ax+b x n a b)
  (define sin:ax+b (Sin (⊕ (⊗ a x) b)))
  (define cos:ax+b (Cos (⊕ (⊗ a x) b)))
  (define (next-integ m)
    (integrate-x^n.sin:ax+b x m a b))
  (cond
    [(> n 0)  (⊕ (⊗ (⊘ 1 a) (Expt x n) sin:ax+b) (⊗ (⊘ (⊖ n) a) (next-integ (- n 1))))]
    [(= n 0)  (⊗ (⊘ 1 a) sin:ax+b)]
    [(= n -1) (⊖ (⊗ (Cos b) (Ci (⊗ a x))) (⊗ (Sin b) (Si (⊗ a x))))] ;;; special function, Ci, Si;
    [(< n -1)
     (define n+1 (+ n 1))
     (⊕ (⊗ (⊘ 1 n+1) (Expt x n+1) cos:ax+b) (⊗ (⊘ a n+1) (next-integ n+1)))]))

(define (sqrt:1-x2 u)
  (Sqrt (⊖ 1 (Sqr u))))

(define (integrate-table-impl u x)
  (when debugging? (displayln (list 'integrate-table-impl u x)))
  (define (integ u) (integrate-table-impl u x))
  (define (free-of-x u) (free-of u x))
  (match u
    [u #:when (free-of u x)       (⊗ u x)]
    [(Sum us)                      (apply ⊕ (map integ us))]
    [(Prod us) #:when (ormap free-of-x us) ; This pattern help eliminate unrelated terms for below TimesTerms pattern.
               (define-values (free non-free) (partition free-of-x us))
               (⊗ (apply ⊗ free) (integ (apply ⊗ non-free)))]
    [(== x) (⊗ 1/2 (Sqr x))]
    [(Expt (== x) -1) (Ln x)] ; x can be complex number.
    [(Expt (== x) u) #:when (free-of u x) (⊘ (Expt x (⊕ 1 u)) (⊕ 1 u))]
    [(Expt u (== x)) #:when (free-of u x) (⊘ (Expt u x) (Ln u))]
    [(Ln (== x))    (⊖ (⊗ (Ln x) x) x)]
    [(Expt (PlusTerms 1 (Sqr x)) -1) (Atan x)]
    [(Abs (== x))   (⊗ (Abs x) x 1/2)]
    [(Exp (rx+s x a b)) (⊘ (Exp (rx+s x a b)) a)]
    [(Sin (rx+s x a b)) (⊘ (Cos (rx+s x a b)) (⊖ a))]
    [(Cos (rx+s x a b)) (⊘ (Sin (rx+s x a b)) a)]
    [(Asin (== x)) (⊗ 1/4 (⊕ (⊗ x (sqrt:1-x2 x)) (⊗ (⊖ (⊗ 2 (Sqr x)) 1) (Asin x))))]
    [(Acos(== x)) (⊗ 1/4 (⊕ (⊗ (⊖ x) (⊖ (sqrt:1-x2 x) (⊗ @pi x))) (⊗ (⊖ 1 (⊗ 2 (Sqr x))) (Asin x))))]
    [(Atan (== x)) (⊗ 1/2 (⊖ (⊗ (⊕ (Sqr x) 1) (Atan x)) x))]
    [(Asinh (== x)) (⊖ (⊗ x (Asinh x)) (Sqrt (⊕ (Sqr x) 1)))]
    [(Acosh (== x)) (⊖ (⊗ x (Acosh x)) (Sqrt (⊕ (Sqr x) -1)))]
    [(Expt (Cos (== x)) (? integer? p)) (integrate-cos^n:x x p)]
    [(Expt (Sin (== x)) (? integer? p)) (integrate-sin^n:x x p)]
    [(TimesTerms (GreedyExpt (Sin (== x)) (? integer? p))
                (GreedyExpt (Cos (== x)) (? integer? q)))
     (integrate-sin^m:x.cos^n:x x p q)]
    [(TimesTerms (GreedyExpt (== x) (? integer? p)) (Exp (rx+s x a b))) (integrate-x^n.e^ax+b x p a b)]
    [(TimesTerms (GreedyExpt (== x) (? integer? p)) (Sin (rx+s x a b))) (integrate-x^n.sin:ax+b x p a b)]
    [(TimesTerms (GreedyExpt (== x) (? integer? p)) (Cos (rx+s x a b))) (integrate-x^n.cos:ax+b x p a b)]
    [(TimesTerms (Sin (== x)) (Exp (rx+s x a b))) ; can be obtained by parts
     (⊘ (⊗ (Exp (rx+s x a b)) (⊖ (⊗ a (Sin x)) (Cos x))) (⊕ (Sqr a) 1))]
    [(TimesTerms (Cos (== x)) (Exp (rx+s x a b)))
     (⊘ (⊗ (Exp (rx+s x a b)) (⊕ (⊗ a (Cos x)) (Sin x))) (⊕ (Sqr a) 1))]
    [(Expt (rx+s x ur us) -n) #:when (and (integer? -n) (< -n -1))
                              (define n-1 (- -1 -n))
                              (⊘ -1 (⊗ n-1 ur (Expt (rx+s x ur us) n-1)))]
    [(Expt (ax2+bx+c x a b c) -1)
     (integrate-1/ax2+bx+c x a b c)]
    [(Expt (ax2+bx+c x a b c) -n) #:when (and (integer? -n) (< -n -1))
                                  (define n-1 (- -1 -n))
                                  (define b2-4ac (⊖ (Sqr b) (⊗ 4 a c)))
                                  (define 2ax+b (⊕ (⊗ 2 a x) b))
                                  (define ax2+bx+c^n-1 (Expt (ax2+bx+c x a b c) n-1))
                                  (⊕ (⊘ (⊖ 2ax+b) (⊗ n-1 b2-4ac ax2+bx+c^n-1))
                                     (⊘ (⊗ -1 (⊖ (⊗ -4 -n) 6) a) (⊗ n-1 b2-4ac (integ (⊘ 1 ax2+bx+c^n-1) x))))]
    [(⊘ (rx+s x ur us) (ax2+bx+c x a b c))
     (define alpha (⊘ ur (⊗ 2 a)))
     (define beta (⊖ us (⊘ (⊗ ur b) (⊗ 2 a))))
     (⊕ (⊗ alpha (Ln (ax2+bx+c x a b c))) (⊗ beta (integrate-1/ax2+bx+c x a b c)))]
    [(⊘ (rx+s x ur us) (Expt (ax2+bx+c x a b c) n)) #:when (and (integer? n) (> n 1))
                                  (define n-1 (- n 1))
                                  (define ax2+bx+c-expr (ax2+bx+c x a b c))
                                  (⊕ (⊘ (⊖ ur) (⊗ 2 n-1 a (Expt ax2+bx+c-expr n-1)))
                                     (⊗ (⊘ (⊕ (⊗ -1 b ur) (⊗ 2 a us)) (⊗ 2 a)) (integ (⊘ 1 (Expt ax2+bx+c-expr n)) x)))]
    [_                           (or (trig-subst u x u) (raise 'integrate-table-failed))]))

(module+ test
  (displayln "TEST - integrate")
  (check-equal? (integrate 1 x) x)
  (check-equal? (integrate x x) (⊗ 1/2 (Sqr x)))
  (check-equal? (integrate (Expt x 3) x) (⊗ 1/4 (Expt x 4)))
  (check-equal? (integrate '(* (cos x) (sin x)) x) '(* -1/2 (expt (cos x) 2)))
  (check-equal? (integrate '(* (sin x) (sin x)) x) '(+ (* 1/2 x) (* -1/2 (cos x) (sin x))))
  (check-equal? (integrate (⊗ 2 x (Cos (Sqr x))) x) '(sin (expt x 2)))
  (check-equal? (integrate '(* 2 x (expt (+ (expt x 2) 4) 5)) x) '(* 1/6 (expt (+ 4 (expt x 2)) 6)))
  (check-equal? (integrate '(* (cos x) (expt 2 (sin x))) x) '(* (expt 2 (sin x)) (expt (ln 2) -1)))
  (check-equal? '(* -1/4 (expt (ln (cos (expt (+ 1 x) 2))) 2))
                (let* [(u (⊕ x 1)) (v (Sqr u))]
                  (integrate (⊘ (⊗ u (Ln (Cos v)) (Sin v)) (Cos v)) x)
                  '(* -1/4 (expt (ln (cos (expt (+ 1 x) 2))) 2))))
  (check-equal? (integrate '(* (+ x 1) (+ x 2)) x) '(+ (* 1/2 (expt (+ 1 x) 2)) (* 1/3 (expt (+ 1 x) 3))))
  (check-equal? (integrate '(* (+ (* 2 x) 1) (cos (+ x (expt x 2)))) x) '(sin (+ x (expt x 2))))
  (check-equal? (integrate '(* 5 x (cos (expt x 2)) (sin (expt x 2))) x) '(* -5/4 (expt (cos (expt x 2)) 2)))
  (check-equal? (integrate '(* (+ (cos x) 2) (+ (sin x) 3)) x)
                '(+ (* 6 x) (* -2 (cos x)) (* -1/2 (expt (cos x) 2)) (* 3 (sin x))))
  (check-equal? (integrate '(* (sin x) (expt (cos x) -4)) x) '(* 1/3 (expt (cos x) -3)))
  (check-equal? (integrate '(* (expt (+ (sin x) 4) 3) (cos x)) x) '(* 1/4 (expt (+ 4 (sin x)) 4)))
  (check-equal? (integrate '(* (+ x 2) (expt (+ (expt x 2) (* 4 x) 2) -1)) x)
                '(* 1/2 (ln (+ 2 (* 4 x) (expt x 2)))))
  (check-equal? (integrate '(* (sin (+ (* a (expt x 2)) (* b (expt x 2)))) x) x)
                '(* -1/2 (expt a -1)
                    (expt (+ 1 (* (expt a -1) b)) -1)
                    (cos (* a (expt x 2) (+ 1 (* (expt a -1) b))))))
  ; definite integral
  (check-equal? (integrate `u x `a `b) '(+ (* -1 a u) (* b u)))
  ; test cases from https://github.com/grzegorzmazur/yacas/blob/master/tests/integrate.yts
  (check-equal? (integrate (⊘ 1 x) x) '(ln x))
  (check-equal? (integrate (Expt x -2) x) '(* -1 (expt x -1)))
  (check-equal? (integrate '(* 6 (expt x -2)) x) '(* -6 (expt x -1)))
  (check-equal? (integrate '(* (+ x 4) (expt (+ x 3) -2)) x)
                '(+ (* -2 (expt (+ 6 (* 2 x)) -1)) (* 1/2 (ln (+ 9 (* 6 x) (expt x 2)))))) ; can be simplified.
  (check-equal? (integrate '(expt (+ (* 4 x x) 1) -1) x) (⊗ 1/2 (Atan (⊗ 2 x))))
  (check-equal? (integrate (⊘ '(+ x -1) '(+ (expt x 2) -1)) x)
                '(+ (* 1/2 (ln (+ -1 (expt x 2)))) (* 1/2 (+ (ln (+ 1 (* -1 x))) (ln (+ 1 x))))))
  ; not supported yet (check-equal? (integrate (⊘ x '(+ (expt x 3) 1)) x) ; need to apart fraction.
  (check-equal? (integrate (⊘ 3 (Sin x)) x) '(* -3 (ln (+ (expt (sin x) -1) (* (expt (sin x) -1) (cos x))))))
  (check-equal? (integrate (Ln x) x) '(+ (* x (ln x)) (* -1 x)))
  (check-equal? (integrate (Expt x 500) x) '(* 1/501 (expt x 501)))
  (check-equal? (integrate (Tan x) x) '(* -1 (ln (cos x))))
  (check-equal? (integrate (Expt (Tan x) -1) x) '(ln (sin x)))
  (check-equal? (integrate (Expt (minus 3 (Sqr x)) -1/2) x) '(* (expt 3 -1/2) (asin (* (expt 3 -1/2) x))))
  ; Erf (check-equal? (integrate (Erf ) x)
  (check-equal? (integrate (⊘ (Sin x) '(+ (* 2 y) 4)) x) '(* -1 (expt (+ (* 2 y) 4) -1) (cos x)))
  ;;; definite integral
  (check-equal? (integrate (Sin x) x 0 'A) '(+ 1 (* -1 (cos A))))
  (check-equal? (integrate (Sqr x) x 0 'A) '(* 1/3 (expt A 3)))
  (check-equal? (integrate (Sin '(* B x)) x 0 'A) '(+ (expt B -1) (* -1 (expt B -1) (cos (* A B)))))
  (check-equal? (integrate (⊘ '(+ (expt x 2) (* 2 x) 1) '(+ x 1)) x 0 'A) '(+ -1/2 (* 1/2 (expt (+ 1 A) 2))))
  (check-equal? (integrate (⊘ '(+ x 1) '(+ (expt x 2) (* 2 x) 1)) x 0 'A) '(* 1/2 (ln (+ 1 (* 2 A) (expt A 2)))))
  ; https://github.com/grzegorzmazur/yacas/blob/master/scripts/integrate.rep/code.ys
  (check-equal? (integrate (Sqrt x) x) '(* 2/3 (expt x 3/2)))
  (check-equal? (integrate (Expt x -1/2) x) '(* 2 (expt x 1/2)))
  (check-equal? (integrate (Expt (Sin x) -1) x) '(* -1 (ln (+ (expt (sin x) -1) (* (expt (sin x) -1) (cos x))))))
  (check-equal? (integrate (Expt (Cos x) -1) x) '(ln (+ (expt (cos x) -1) (* (expt (cos x) -1) (sin x)))))
  (check-equal? (integrate '(* x (ln x)) x) '(+ (* -1/4 (expt x 2)) (* 1/2 (expt x 2) (ln x))))
  (check-equal? (integrate (Expt (Sin x) -2) x) '(* (expt (sin x) -1) (cos x)))
  (check-equal? (integrate (Expt (Cos x) -2) x) '(* (expt (cos x) -1) (sin x)))
  (check-equal? (integrate '(expt (* (sin x) (tan x)) -1) x) '(* -1 (expt (sin x) -1)))
  (check-equal? (integrate '(* (tan x) (expt (cos x) -1)) x) '(expt (cos x) -1))
  (check-equal? (integrate (Expt (Sinh x) -2) x) '(* 4 (expt (+ -2 (* 2 (expt @e (* -2 x)))) -1))) ; -Coth(x)-1
  (check-equal? (integrate (Expt (Cosh x) -2) x) '(* 4 (expt (+ 2 (* 2 (expt @e (* -2 x)))) -1))) ; Tanh(x)+1
  (check-= (N (subst (⊖ (⊖ (⊘ 1 (Tanh x))) (integrate (Expt (Sinh x) -2) x)) x @i)) 1 0.0001)
  (check-= (N (subst (⊖ (Tanh x) (integrate (Expt (Cosh x) -2) x)) x @i)) -1 0.0001)
  (check-equal? (integrate (Expt (⊗ (Sinh x) (Tanh x)) -1) x) '(* -2 (expt (+ (* -1 (expt @e (* -1 x))) (expt @e x)) -1)))
  (check-equal? (integrate (⊗ (Tanh x) (Expt (Cosh x) -1)) x) '(* -2 (expt (+ (expt @e (* -1 x)) (expt @e x)) -1)))
  (check-equal? (integrate '(* (expt @e (* 'n x)) (sin (* 'm x))) x)
                '(* (expt @e (* x 'n)) (expt 'm -1) (expt (+ 1 (* (expt 'm -2) (expt 'n 2))) -1)
                    (+ (* (expt 'm -1) 'n (sin (* x 'm))) (* -1 (cos (* x 'm))))))
  (check-equal? (integrate '(* (ln x) (expt x 3)) x) '(+ (* -1/16 (expt x 4)) (* 1/4 (expt x 4) (ln x))))
  (check-equal? (integrate '(* (ln (* 'A x)) (expt x 2)) x)
                '(* (expt 'A -3) (+ (* -1/9 (expt x 3) (expt 'A 3)) (* 1/3 (expt x 3) (expt 'A 3) (+ (ln x) (ln 'A))))))
  (check-equal? (integrate (Sin (Ln x)) x) '(* 1/2 x (+ (* -1 (cos (ln x))) (sin (ln x)))))
  (check-equal? (integrate (Cos (Ln x)) x) '(* 1/2 x (+ (cos (ln x)) (sin (ln x)))))
  (check-equal? (integrate (⊘ 1 '(* x (ln x))) x) '(ln (ln x)))
  (check-equal? (integrate (Sinh x) x) '(* 1/2 (+ (expt @e (* -1 x)) (expt @e x))))
  (check-equal? (integrate (Expt (Sinh x) 2) x) '(* 1/4 (+ (* -1/2 (expt @e (* -2 x))) (* 1/2 (expt @e (* 2 x))) (* -2 x))))
  (check-equal? (integrate (Expt (Sinh x) -1) x) '(+ (ln (+ 1 (* -1 (expt @e (* -1 x))))) (ln (+ 1 (expt @e (* -1 x))))))
  (check-equal? (integrate (Cosh x) x) '(* 1/2 (+ (* -1 (expt @e (* -1 x))) (expt @e x))))
  (check-equal? (integrate (Expt (Cosh x) 2) x) '(* 1/4 (+ (* -1/2 (expt @e (* -2 x))) (* 1/2 (expt @e (* 2 x))) (* 2 x))))
  (check-equal? (integrate (Expt (Cosh x) -1) x) '(* -2 (asin (* (expt @e (* -1 x)) (expt (+ 1 (expt @e (* -2 x))) -1/2)))))
  (check-equal? (integrate (Tanh x) x) '(ln (+ (expt @e (* -1 x)) (expt @e x))))
  (check-equal? (integrate (Expt (Tanh x) -1) x) '(ln (+ (* -1 (expt @e (* -1 x))) (expt @e x))))
  (check-equal? (integrate (⊘ (Tanh x) (Cosh x)) x) '(* -2 (expt (+ (expt @e (* -1 x)) (expt @e x)) -1)))
  (check-equal? (integrate (Abs x) x) '(* 1/2 x (abs x)))
  (check-equal? (integrate (Atan x) x)
                '(* 1/2 (+ (* -1 x) (* (asin (* x (expt (+ 1 (expt x 2)) -1/2))) (+ 1 (expt x 2))))))
  (check-equal? (integrate (Acos x) x)
                '(* 1/4 (+ (* -1 x (+ (expt (+ 1 (* -1 (expt x 2))) 1/2) (* -1 @pi x))) (* (asin x) (+ 1 (* -2 (expt x 2)))))))
  (check-equal? (integrate (Asin x) x)
                '(* 1/4 (+ (* x (expt (+ 1 (* -1 (expt x 2))) 1/2)) (* (asin x) (+ -1 (* 2 (expt x 2)))))))
  (check-equal? (integrate (Atanh x) x)
                '(* 1/2 (+ (* (ln (+ 1 x)) (+ 1 x))
                           (* -1 (+ 1 x))
                           (* -1 (+ (* (ln (+ 1 (* -1 x))) (+ 1 (* -1 x))) (* -1 (+ 1 (* -1 x))))))))
  (check-equal? (integrate (Acosh x) x) '(+ (* -1 (expt (+ 1 (expt x 2)) 1/2)) (* x (ln (+ x (expt (+ 1 (expt x 2)) 1/2))))))
  (check-equal? (integrate (Asinh x) x) '(+ (* -1 (expt (+ -1 (expt x 2)) 1/2)) (* x (ln (+ x (expt (+ -1 (expt x 2)) 1/2))))))
  (check-equal? (integrate (⊘ 'C '(+ n (* -1 (expt x 2)))) x)
                (normalize '(* -2 C (expt (* -4 n) -1/2) (asin (* 2 x (expt (* -4 n) -1/2) (expt (+ 1 (* -1 (expt x 2) (expt n -1))) -1/2))))))
  (check-equal? (integrate (⊘ 'C '(expt (+ 'n (* -1 (expt x 2))) 1/2)) x)
                '(* C (expt 'n -1/2) (asin (* x (expt 'n -1/2))))) ; subst with tri funcs.
  (check-equal? (integrate (⊘ 'C '(+ A (* B (expt x 2)))) x)
                (normalize '(* 2 C (expt (* 4 A B) -1/2) (asin (* 2 x (expt (* 4 A B) -1/2) (expt (+ 1 (* (expt x 2) (expt A -1) B)) -1/2) B)))))
  ;-------
  (check-equal? (integrate '(expt (+ (expt @e x) (expt @e (* -1 x))) -1) x) '(asin (* (expt @e x) (expt (+ 1 (expt @e (* 2 x))) -1/2))))
  (check-equal? (integrate '(* (expt @e x) (expt (+ 1 (expt @e (* 2 x))) -1)) x)
                '(asin (* (expt @e x) (expt (+ 1 (expt @e (* 2 x))) -1/2))))
  (check-equal? (integrate '(* (tan x) (expt (cos x) -3)) x) '(* 1/3 (expt (cos x) -3)))
  (check-equal? (integrate '(* (+ (sin x) 1) (+ (cos x) 1)) x)
                '(+ x (* -1 (cos x)) (* -1/2 (expt (cos x) 2)) (sin x)))
  (check-equal? (integrate (⊘ '(+ x 2) '(+ (expt x 2) (* 4 x) 2)) x)
                '(* 1/2 (ln (+ 2 (* 4 x) (expt x 2)))))
  (check-equal? (integrate '(* (sin (+ (* a (expt x 2)) (* b (expt x 2)))) x) x)
                '(* -1/2 (expt a -1) (expt (+ 1 (* (expt a -1) b)) -1) (cos (* a (expt x 2) (+ 1 (* (expt a -1) b))))))
  (check-equal? (integrate '(expt (* (+ (* 2 x) 3) (expt (+ (* 4 x) 5) 1/2)) -1) x)
                '(asin (* (expt (+ 5 (* 4 x)) 1/2) (expt (+ 6 (* 4 x)) -1/2))))
  (check-equal? (integrate (normalize '(expt (+ (expt x 2) (* 2 x) 1) -1)) x) '(* -2 (expt (+ 2 (* 2 x)) -1)))
  (check-equal? (integrate (normalize '(expt (+ (expt x 2) (* 2 x) 2) -1)) x)
                '(asin (* 1/2 (expt (+ 1 (* 1/4 (expt (+ 2 (* 2 x)) 2))) -1/2) (+ 2 (* 2 x)))))
  (check-equal? (integrate (normalize '(expt (+ (expt x 2) (* 3 x) 1) -1)) x) '(* -1 (expt 5 -1/2) (+ (ln (+ 1 (* -1 (expt 5 -1/2) (+ 3 (* 2 x))))) (ln (+ 1 (* (expt 5 -1/2) (+ 3 (* 2 x))))))))
  (check-equal? (integrate (⊘ x '(+ (expt x 2) (* 3 x) 1)) x)
                '(+ (* 3/2 (expt 5 -1/2) (+ (ln (+ 1 (* -1 (expt 5 -1/2) (+ 3 (* 2 x))))) (ln (+ 1 (* (expt 5 -1/2) (+ 3 (* 2 x)))))))
                    (* 1/2 (ln (+ 1 (* 3 x) (expt x 2))))))
  (check-equal? (integrate (⊘ '(+ x 4) '(+ (expt x 2) (* 3 x) 1)) x)
                '(+ (* -5/2 (expt 5 -1/2) (+ (ln (+ 1 (* -1 (expt 5 -1/2) (+ 3 (* 2 x))))) (ln (+ 1 (* (expt 5 -1/2) (+ 3 (* 2 x)))))))
                    (* 1/2 (ln (+ 1 (* 3 x) (expt x 2))))))
  ;--
  (check-equal? (integrate (⊘ (Cos x) '(+ (expt (sin x) 2) (* 3 (sin x)) 4)) x)
                '(* 2 (expt 7 -1/2) (asin (* 3 (expt 7 -1/2) (expt (+ 1 (* 9/7 (expt (+ 1 (* 2/3 (sin x))) 2))) -1/2) (+ 1 (* 2/3 (sin x)))))))
  (check-equal? (integrate (⊘ '(* 2 x) '(+ (expt x 4) 1)) x) '(asin (* (expt x 2) (expt (+ 1 (expt x 4)) -1/2))))
  (check-equal? (integrate '(* 3 (cos x) (expt (* (+ (* 5 (sin x)) 1) (expt (+ (* 4 (sin x)) 7) 1/2)) -1)) x)
                '(* -3 (expt 155 -1/2)
                    (+ (ln (+ 1 (* -5 (expt 155 -1/2) (expt (+ 7 (* 4 (sin x))) 1/2))))
                       (ln (+ 1 (* 5 (expt 155 -1/2) (expt (+ 7 (* 4 (sin x))) 1/2)))))))
  (check-equal? (integrate (Expt (Sin x) 3) x) '(+ (* -1/3 (expt (sin x) 2) (cos x)) (* -2/3 (cos x))))
  (check-equal? (integrate (Expt (Cos x) 4) x) '(+ (* 1/4 (expt (cos x) 3) (sin x)) (* 3/4 (+ (* 1/2 x) (* 1/2 (cos x) (sin x))))))
  (check-equal? (integrate (⊗ (Expt (Cos x) 3) (Expt (Cos x) 3)) x)
                '(+ (* 1/6 (expt (cos x) 5) (sin x))
                    (* 5/6 (+ (* 1/4 (expt (cos x) 3) (sin x))
                              (* 3/4 (+ (* 1/2 x) (* 1/2 (cos x) (sin x))))))))
  (check-equal? (integrate (⊘ '(* 2 x) '(+ (expt x 4) 1)) x) '(asin (* (expt x 2) (expt (+ 1 (expt x 4)) -1/2))))
  (check-equal? (integrate (Expt (Tan x) 3) x) '(+ (* 1/2 (expt (cos x) -2)) (* 1/3 (ln (expt (cos x) 3)))))
  (check-equal? (integrate (Expt (Tan x) 2) x) '(+ (* -1 x) (* (expt (cos x) -1) (sin x))))
  (check-equal? (integrate (diff (Acos x) x) x) '(* -1 (asin x)))
  (check-equal? (integrate (diff (Asin x) x) x) (Asin x))
  (check-equal? (integrate (reduce (diff (Atan x) x)) x) (Atan x))
  (check-equal? (integrate (diff (Si x) x) x) (Si x))
  (check-equal? (integrate (diff (Ci x) x) x) (Ci x))
  (check-equal? (integrate (Sqrt (Sqr x)) x) 
                '(* (expt x 2) (piecewise (-1/2 (< x 0)) (1/2 (>= x 0)))))
  )

  
