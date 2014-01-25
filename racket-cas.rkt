#lang racket
; Short term:
;   - in-terms  ( in-terms/proc is done )
;   - polynomial?  
;   - use multivariable polynomial-quotient/remainder to simplify trig (cos^2+sin^2=1)
;   - power-expand
;   - Implement Integer pattern that accepts @n as an integer
;   - split expand into expand-one and expand (-all)
;   - finish toghether
;   - examine automatic simplification of output of (diff '(expt x x) x)
; Ideas:
;   - implement bfracket where big floats are numbers
;   - add arctan
;   - detect linear equations in solve
;   - add factor
;   - use factor in solve
;   - unparse (for better presentation of results)
;   - tex
;   - algorithms from the book A=B
;   - add Groebner bases
;   - use Groebner bases in solve
;   - use Gruntz algorithm to compute limit
;   - use "poor man's integrator" to implement integrate
;   - symbolic sums (see https://github.com/soegaard/bracket/blob/master/polynomials/poly.rkt)

(provide (all-defined-out))
(require "math-match.rkt" racket/match math/flonum math/number-theory math/special-functions
         (for-syntax syntax/parse racket/syntax racket/format))
(module+ test (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))

;;; A SYMBOLIC EXPRESSION is :
;;;   <sym> ::= <num> | <var> | (<var> <sym> ...)
;;; where
;;;   <num> is a Racket number
;;;   <var> is a Racket symbol
;;; Expressions of the form (<var> <sym> ...) will be called applications.

;;; SYMBOLIC CONSTANTS
(define @e  '@e)  ; Euler's constant
(define @pi '@pi) ; pi
(define @n  '@n)  ; stands for an arbitrary natural number
(define @p  '@p)  ; stands for an arbitrary integer

;;; PATTERN MATCHERS
; In order to eventually define the patterns ⊕, ⊗ and k⊗ we need a few helpers.

(define-syntax (define-predicate-matcher stx)
  (syntax-parse stx
    [(_ <id> pred)
     #'(define-match-expander <id> (λ(stx) (syntax-case stx () [(_ id) #'(? pred id)])))]))

; The pattern (num: x) matches a number and binds x to the number.
(define-predicate-matcher num: number?)
; The pattern (var: x) matches a variable and binds x to the variable.
(define-predicate-matcher var: symbol?)
; The pattern (app: op args) matches an application of the form (<var> <sym> ...)
; and binds op to the operator-variable and binds args to the arguments (a list of <sym>s)
(define-match-expander app: (λ(stx) (syntax-case stx () [(_ op args) #'(list-rest (var: op) args)])))

(module+ test
  (check-equal? (match 42 [(num: x) x]) 42)
  (check-equal? (match 'a [(var: x) x]) 'a)
  (check-equal? (match '(+ a 42) [(app: op xs) (list op xs)]) '(+ (a 42))))

; The pattern (bind: x v) matches anything and binds x to v.
(define-match-expander bind: (λ (stx) (syntax-parse stx [(_ x r)  #'(app (λ(__) r) x)])))
(module+ test (check-equal? (match 41 [(bind: x 42) x]) 42))

(define-match-expander Integer 
  (λ (stx) (syntax-parse stx [(_ u)  #'(or (? number? (and (? integer? u)))
                                           (and (quote @n) (bind: u '@n))
                                           (and (quote @p) (bind: u '@n)))])))
(module+ test 
  (check-equal? (match 41 [(Integer x) x]) 41)
  (check-equal? (match '@n [(Integer x) x]) '@n)
  (check-equal? (match '@foo [(Integer x) x] [_ 'foo]) 'foo))

;; The pattern ⊕ matches various sums
;;  (⊕ x y) matches (+ a b)       and binds x->a, y->b
;;  (⊕ x y) matches (+ a b c ...) and binds x->a, y->(+ b c ...)
(define-match-expander ⊕
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list '+ u v) (list-rest '+ u (app (λ(ys) (cons '+ ys)) v)))]
      [(_ u)       #'(list '+ u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(plus u ...)] [_ (identifier? stx) #'plus])))

(module+ test 
  (check-equal? (match '(+ a b)   [(⊕ u v) (list u v)]) '(a b))
  (check-equal? (match '(+ a b c) [(⊕ u v) (list u v)]) '(a (+ b c))))

;; The pattern ⊗ matches various products
;;  (⊗ x y) matches (* a b)       and binds x->a, y->b
;;  (⊗ x y) matches (* a b c ...) and binds x->a, y->(* b c ...)
(define-match-expander ⊗
  (λ (stx)
    (syntax-parse stx
      [(_ u v)
       #'(or (list '* u v) (list-rest '* u (app (λ(ys) (cons '* ys)) v)))]
      [(_ u v w)
       #'(or (⊗ u (⊗ v w)) (⊗ u (⊗ w v)))]
      [(_ u               )   #'(list '* u)]
      [_ (error '⊗-match-expander (~a "only (⊗ u v) and (⊗ u) works, got: " stx))]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(times u ...)][_ (identifier? stx) #'times])))

(module+ test (require rackunit)
  (check-equal? (match '(* a b)   [(⊗ x y) (list x y)]) '(a b))
  (check-equal? (match '(* a b c) [(⊗ x y) (list x y)]) '(a (* b c))))


;; The pattern (k⊗ r x) matches expressions that can be seen
;; as a product of a number and an expression.
;; Here s is a number, y is a variable and a b c are expressions:
;;   (k⊗ r x) matches (* s a b ...) and binds r->s, x->(* a b c ...)
;;   (k⊗ r x) matches (*   a b ...) and binds r->1, x->(* a b c ...)
;;   (k⊗ r x) matches s and binds r->1, x->s
;;   (k⊗ r x) matches y and binds r->1, x->y
(define-match-expander k⊗
  (λ (stx)
    (syntax-parse stx
      [(_ k u)
       (syntax/loc stx
         (or (list      '* (num:  k) u)
             (list-rest '* (num:  k) (app (λ(ys) (cons '* ys)) u))
             (and (bind: k 1) (num: u))
             (and (bind: k 1) (var: u))
             (and (bind: k 1) (and u (⊗ _ _)))
             (and (bind: k 1) (and u (app: _ _)))))])))

(module+ test
  (check-equal? (match '(* 3 a b) [(k⊗ x y) (list x y)]) '(3 (* a b)))
  (check-equal? (match '3         [(k⊗ x y) (list x y)]) '(1 3))
  (check-equal? (match 'a         [(k⊗ x y) (list x y)]) '(1 a))
  (check-equal? (match '(* a b)   [(k⊗ x y) (list x y)]) '(1 (* a b)))
  (check-equal? (match '(* a b c) [(k⊗ x y) (list x y)]) '(1 (* a b c)))
  (check-equal? (match '(sin x)   [(k⊗ r u) (list r u)]) '(1 (sin x))))

;;; The patterm (Sum us) matches a sum of the form (+ u ...) and binds us to (list u ...)
(define-match-expander Sum  (λ (stx) (syntax-case stx () [(_ id) #'(list '+ id (... ...))])))
;;; The patterm (Prod us) matches a product of the form (* u ...) and binds us to (list u ...)
(define-match-expander Prod (λ (stx) (syntax-case stx () [(_ id) #'(list '* id (... ...))])))

#|
;;; ASSUMPTIONS
(define assumptions (make-hash))
(define (get-assumptions var)     (hash-ref assumptions var '()))
(define (add-assumption! var tag) (hash-set! assumptions var (cons tag (get-assumptions tag))))
(define (assume-real var)         (add-assumption! var 'real))
(define (assume-positive var)     (add-assumption! var 'positive))
(define (assume-negative var)     (add-assumption! var 'negative))

(define (Positive? u)
  (and (math-match u
         [r       (positive? r)]
         [r.bf    (bfpositive? r.bf)]
         [x       (member 'positive (get-assumptions x))]
         [(⊗ u v) (let ([pu (Positive? u)] [pv (Positive? v)])
                    (or (and pu pv) (and (not pu) (not pv))))]
         [(⊕ u v) (and (Positive? u) (Positive? v))]
         ; ... ? Missing cases ?
         [else #f])
       #t))

(module+ test
  (check-false (Positive? x))
  (assume-positive x)
  (check-true  (Positive? 1))
  (check-false (Positive? -1))
  (check-true  (Positive? x))
  (check-false (Positive? (Sqrt x)) #f))  ; TODO xxx
|#

;; <<= defines an order on the set of symbolic expressions
;; Sorting the terms in a sum according to this order, brings together
;; terms that can be rewritten e.g. (+ x x) -> (* 2 x).
;; The ordering also brings together similar factors of a product.
;; Note: If you find yourself in an infinite loop, check whether
;;       (<<= u v) and (<<= v u) gives the same or diffent results.
;;       If they give the same result, the bug is most likely in <<=.

(define (<<= u v)
  (or (equal? u v)
      (<< u v)))

(define (<< s1 s2)
  ; (displayln (list '<<= s1 s2)) ; uncomment in case of infinite loop
  (math-match* (s1 s2)
    ; Case: at least one number
    [(r s) (< r s)]
    [(r _) #t]
    [(u r) #f]
    ; Case: at leat one big float
    [(r.bf s.bf) (bf< r.bf s.bf)]
    [(r.bf _) #t]
    [(u r.bf) #f]
    ; Case: At least one symbol
    [(x y) (symbol<? x y)] 
    [(u x) (not (<< x u))]
    [(x (⊗ r x)) (< 1 r)]  ; x ~ (* 1 x)
    [(x (⊗ r u)) (<< x u)]
    [(x (⊗ u _)) (<< x u)]
    [(x (Expt x v)) (<< 1 v)]  ; (Note: x ~ (Expt x 1)    
    ; Case: At least one product of ...
    [((k⊗ r u) (k⊗ s u)) (< r s)]
    [((k⊗ r u) (k⊗ s v)) ; (Note: neither u nor v are numbers)
     (math-match* (u v)
       ; ... at least one symbol
       [(x x) #f]
       [(x y) (symbol<? x y)]
       [(u x) (not (<< x u))]
       ; ... at most one symbol
       [(x (Expt x v)) (<< 1 v)]  ; (Note: x ~ (Expt x 1)
       [(x (Expt u v)) (<< x u)]
       [(x (⊗ r x))    (<< 1 r)]  ; (Note: x ~ (* 1 x) )
       [(x (⊗ u v))    (<< x u)]  ; (Note: x ~ (* 1 x) )
       [(x _) #t]       
       ; ... two non-symbols
       [(u (Expt u a)) (<< 1 a)]  ; Note u ~ (Expt u 1)
       [((Expt u a) u) (<< a 1)]  ; Note u ~ (Expt u 1)
       [((Expt u a) (Expt u b)) (<< a b)]
       [((Expt u a) (Expt v b)) (<< u v)]
       [((Expt _ _) (app: _ _)) #t] ; (Note: Place powers before applications)
       [((app: _ _) (Expt _ _)) #f]
       ; ... two non-powers and non-symbols  (i.e. two products, sums or applications)
       [((⊗ u a) (⊗ u b)) (<< a b)]
       [((⊗ u a) (⊗ v b)) (<< u v)]  ; (Note: the least factor is first, so u<<a and v<<b)
       [((⊗ _ _) _) #t]
       [(_ (⊗ _ _)) #f]
       ; ... two non-symbol/power/products  (i.e. sums or applications)
       [((⊕ u a) (⊕ u b)) (<< a b)]
       [((⊕ u a) (⊕ v b)) (<< u v)]
       [(_ (⊕ v b)) #t] ; xxx
       [((⊕ v b) _) #f] ; xxx
       ; ... two non-symbol/power/products/sums  (i.e. applications)
       [((app: f us) (app: g vs))
        (or (symbol<? f g)
            (and (eq? f g)
                 (let ([l (length us)] [m (length vs)])
                   (or (< l m)
                       (and (= l m)
                            (for/and ([u us] [v vs])
                              (<<= u v)))))))]
       ; no other possibilities left
       [(_ _) (displayln (list s1 s2)) (error '<< "internal error: missing a case")])]
    [(_ _) (displayln (list s1 s2)) (error '<< "internal error: missing a case")]))

(module+ test
  (check-equal? (<<= 1 2) #t)
  (check-equal? (<<= 2 1) #f)
  (check-equal? (<<= 1 x) #t)
  (check-equal? (<<= x 1) #f)
  (check-equal? (<<= x y) #t)
  (check-equal? (<<= y x) #f)
  (check-equal? (<<= (⊗ 2 x) (⊗ 2 y)) #t)
  (check-equal? (<<= (⊗ 2 x) (⊗ 3 x)) #t)
  (check-equal? (<< '(* a b) '(* 2 c)) #t)
  (check-equal? (<< '(* 2 c) '(* a b)) #f)
  (check-equal? (<<= (Expt x 2) (⊗ 5 x)) #f)
  (check-equal? (<<= (⊗ 5 x) (Expt x 2)) #t)
  (check-equal? (<<= '(expt x 3) '(expt x 2)) #f)
  (check-equal? (<<= '(expt x 2) '(expt x 3)) #t)
  (check-equal? (<<= '(* x (expt y 2)) '(* (expt x 2) y)) #t)
  (check-equal? (<<= '(* (expt x 1) (expt y 2)) '(* (expt x 2) (expt y 1))) #t)
  (check-equal? (<<= '(* (expt x 2) y) '(* x (expt y 2))) #f)
  (check-equal? (<<= '(cos (expt x 3)) '(expt x 2)) #f)
  (check-equal? (<<= '(expt x 2) '(cos (expt x 3))) #t)
  (check-equal? (<<= x '(* 2 x)) #t)
  (check-equal? (<<= '(* 2 x) x) #f)
  (check-equal? (<<= '(+ (* 2 h (expt x 2)) (*   (expt h 2) x))
                     '(+ (*   h (expt x 2)) (* 2 (expt h 2) x))) #f)
  (check-equal? (<<= '(+ (*   h (expt x 2)) (* 2 (expt h 2) x))
                     '(+ (* 2 h (expt x 2)) (*   (expt h 2) x))) #t)
  (check-equal? (<<= '(* a (expt (+ 1 y) 2)) 'c) #t)
  (check-equal? (<< '(* 2 (+ -1.0 x)) '(* 3 (expt (+ -1.0 x) 2))) #t))

;; (⊕ u ...) in an expression context expands to (plus u ...)
;; That is: Elsewhere use ⊕ in order to add expressions.
;; Note: plus assumes the expressions are canonical.
(define (plus . us) (foldl plus2 0 us))
(define (plus2 s1 s2)
  ; '(+ (* 2 c) (* a b) (* 3 c))
  ; (displayln (list 'plus2 s1 s2))
  ; Note: all recursive calls must reduce size of s1
  ; Note: This is the first use of math-match in this file.
  ; The conventions in math-match are:
  ;   r and s matches only numbers
  ;   x and y matches only symbols
  ;   @e and @pi matches only '@e and '@pi  
  (math-match* (s1 s2)  
    [(0 u) u]
    [(u 0) u]
    [(r s)    (+ r s)]
    ; [(r.bf s.bf) (bf+ r.bf s.bf)] ; xxx
    ; [(r s.bf)    (bf+ (bf r) s.bf)]  ; xxx
    ; [(r.bf s)    (bf+ r.bf (bf s))]  ; xxx
    [(u s) (plus2 s u)]  ; ok since u can not be a number, we have that s <<= u
    [(u u) (times2 2 u)] 
    [((k⊗ r u) (k⊗ s u)) (times2 (+ r s) u)]
    [((k⊗ r u) (k⊗ s v)) #:when (<<= v u) (plus2 s2 s1)]
    [((⊕ u v) (⊕ _ _)) (plus2 u (plus2 v s2))]
    [((⊕ u v) _) (plus2 u (plus2 v s2))]
    [(u (⊕ v w)) 
     (if (<<= u v)
         (match (plus2 u v)
           [(Sum _) (match w 
                      [(Sum ws) (list* '+ u v ws)]
                      [_        (list  '+ u v w)])]
           [u+v     (plus2 u+v w)])
         (plus2 v (plus2 u w)))]
    [(_ _) (list '+ s1 s2)]))

(module+ test
  (check-equal? (⊕) 0)
  (check-equal? (⊕ 1) 1)
  (check-equal? (⊕ 1 2) 3)
  (check-equal? (⊕ 0 x) x)
  (check-equal? (⊕ x 0) x)
  (check-equal? (⊕ 1 x) '(+ 1 x))
  (check-equal? (⊕ x 1) '(+ 1 x))
  (check-equal? (⊕ x y) '(+ x y))
  (check-equal? (⊕ y x) '(+ x y))
  (check-equal? (⊕ 1 x y) '(+ 1 x y))
  (check-equal? (⊕ x 1 y) '(+ 1 x y))
  (check-equal? (⊕ x y 1) '(+ 1 x y))
  (check-equal? (⊕ 1 y x) '(+ 1 x y))
  (check-equal? (⊕ y 1 x) '(+ 1 x y))
  (check-equal? (⊕ y x 1) '(+ 1 x y))
  (check-equal? (⊕ x x) '(* 2 x))
  (check-equal? (⊕ x x x) '(* 3 x))
  (check-equal? (⊕ (⊗ 2 x) (⊗ 3 x)) '(* 5 x))
  (check-equal? (⊕ (⊗ 2 x) (⊗ 3 y)) '(+ (* 2 x) (* 3 y)))
  (check-equal? (⊕ (⊗ 3 y) (⊗ 2 x)) '(+ (* 2 x) (* 3 y)))
  (check-equal? (⊕ x (⊕ 1 x)) '(+ 1 (* 2 x)))
  (check-equal? (⊕ (⊕ 1 x) (⊕ 3 y)) '(+ 4 x y))
  (check-equal? (⊕ y x y x y) '(+ (* 2 x) (* 3 y)))
  (check-equal? (⊕ x y x z 7 x y x) '(+ 7 (* 4 x) (* 2 y) z))
  (check-equal? (⊕ x 1 y x) '(+ 1 (* 2 x) y))
  (check-equal? (⊕ (⊗ 2 x y) (⊗ 3 x y)) (⊗ 5 x y))
  (check-equal? (⊕ '(sin x) '(sin x)) '(* 2 (sin x)))
  (check-equal? (⊕ '(sin x) 3 '(sin x)) '(+ 3 (* 2 (sin x))))
  (check-equal? (⊕ '(cos x) '(sin x)) '(+ (cos x) (sin x)))
  (check-equal? (⊕ '(expt x 3) (⊗ 2 '(sin x))) '(+ (expt x 3) (* 2 (sin x))))
  (check-equal? (⊕ x (Expt x 3) (⊖ x)) (Expt x 3))
  (check-equal? (⊕ (Sin x) (⊗ 2 (Sin x))) '(* 3 (sin x)))
  (check-equal? (⊕ 1 x (⊗ -1 (⊕ 1 x))) 0)
  (check-equal? (normalize '(+ (f x) (f y) (f x))) '(+ (* 2 (f x)) (f y)))
  (check-equal? (normalize '(+ (f x) (f (+ h x)) (f (+ (* 2 h) x))))
                '(+ (f x) (f (+ h x)) (f (+ (* 2 h) x)))))

;; (⊗ u ...) in an expression context expands to (times u ...)
;; That is: Elsewhere use ⊗ in order to multiply expressions.
;; Note: times assumes the expressions are canonical.
(define (times . xs) (foldl times2 1 xs))
(define (times2 s1 s2)
  ; (displayln (list 'times2 s1 s2)) ; uncomment in time of need
  (math-match* (s1 s2)
    [(0 u) 0] [(u 0) 0]
    [(1 u) u] [(u 1) u]
    [(r s) (* r s)]
    ; [(r.bf s.bf) (bf* r.bf s.bf)]    ; xxx
    ; [(r s.bf)    (bf* (bf r) s.bf)]  ; xxx
    ; [(r.bf s)    (bf* r.bf (bf s))]  ; xxx
    [(u s) #:when (math-match u
                    [(Expt v w) (<<= s v)]
                    [_          (<<= s u)])
           (times2 s u)]
    [(r x) (list '* r x)]
    [(u u) (Expt u 2)]
    [(u (Expt u v)) #:when (not (integer? u)) (Expt u (⊕ 1 v))]
    [((Expt u v) u) #:when (not (integer? u)) (Expt u (⊕ 1 v))]
    [((Expt u v) (Expt u w)) (Expt u (⊕ v w))]
    [(x y) (if (symbol<? x y) (list '* x y) (list '* y x))]
    ; all recursive calls must reduce size of s1 wrt <<=
    [((⊗ u v) (⊗ _ __)) (times2 u (times2 v s2))]
    [((⊗ u v) w) (times2 s2 s1)]
    [(u (⊗ v w))
     (if (<<= u v)
         (match (times2 u v)
           [(Prod _) (match w 
                       [(Prod ws) (list* '* u v ws)]
                       [_         (list  '* u v w)])]
           [u*v       (times2 u*v w)])
         (times2 v (times2 u w)))]
    [(_ _) (if (<<= s1 s2) (list '* s1 s2) (list '* s2 s1))]))

(module+ test
  (check-equal? (⊗) 1)
  (check-equal? (⊗ 2) 2)
  (check-equal? (⊗ 2 3) 6)
  (check-equal? (⊗ 0 x) 0)
  (check-equal? (⊗ x 0) 0)
  (check-equal? (⊗ 1 x) x)
  (check-equal? (⊗ x 1) x)
  (check-equal? (⊗ 2 x) '(* 2 x))
  (check-equal? (⊗ x 2) '(* 2 x))
  (check-equal? (⊗ x y) '(* x y))
  (check-equal? (⊗ y x) '(* x y))
  (check-equal? (⊗ 2 y x) '(* 2 x y))
  (check-equal? (⊗ y x 2) '(* 2 x y))
  (check-equal? (⊗ (⊗ 2 x) (⊗ 3 y)) '(* 6 x y))
  (check-equal? (⊗ x x x) (Expt x 3))
  (check-equal? (⊗ x x x x) (Expt x 4))
  (check-equal? (⊗ (Expt x 3) x) (Expt x 4))
  (check-equal? (⊗ x (Expt x 3)) (Expt x 4))
  (check-equal? (⊗ (Expt x 3) (Expt x 4)) (Expt x 7))
  (check-equal? (⊗ x (Expt x -1)) 1)
  (check-equal? (⊗ y (Expt x 2)) '(* (expt x 2) y))
  (check-equal? (⊗ x (Cos x)) '(* x (cos x)))
  (check-equal? (⊗ (⊗ x y) (Sqr (⊗ x y))) (⊗ (Expt x 3) (Expt y 3)))
  (check-equal? (⊗ 2 (Expt 2 1/2)) '(* 2 (expt 2 1/2)))
  (check-equal? (⊗ (Expt 2 1/2) 2) '(* 2 (expt 2 1/2))))

(define-syntax (define-function stx)
  (syntax-parse stx
    [(_ Name Name: sym-name expr)
     (syntax/loc stx
       (begin
         (define-match-expander Name
           (λ (stx) (syntax-parse stx [(_ u) #'(list 'sym-name u)]))
           (λ (stx) (syntax-parse stx [(_ u) #'(Name: u)] [_ (identifier? stx) #'Name:])))
         (define Name: expr)))]))

(define-function Gamma Gamma: gamma
  (λ (u)
    (math-match u
      [n (gamma n)]
      [p 'undefined]
      [r (gamma r)]
      [r.bf (bfgamma r.bf)]
      [_ `(gamma ,u)])))

(define-syntax (define-integer-function stx)
  (syntax-parse stx
    [(_ Name Name: name)
     (syntax/loc stx
       (define-function Name Name: name
         (λ (u)
           (math-match u
             [n (name n)]
             [_ `(name ,u)]))))]))

(define-integer-function Factorial Factorial: factorial)
(define-integer-function Prime? Prime?: prime?)
(define-integer-function Odd-prime? Odd-prime?: odd-prime?)
(define-integer-function Nth-prime Nth-prime: nth-prime)
(define-integer-function Random-prime Random-prime: random-prime)
(define-integer-function Next-prime Next-prime: next-prime)
(define-integer-function Prev-prime Prev-prime: prev-prime)
(define-integer-function Divisors divisors: divisors)

; normalize will given a non-canonical form u 
; return the corresponding canonical form.
(define (normalize u)
  (define n normalize)
  (math-match u
    [r r]
    [r.bf r.bf]
    [x x]
    [(⊕ u)             (n u)]
    [(⊕ u v)           (⊕ (n u) (n v))]
    [(⊗ u)             (n u)]
    [(⊗ u v)           (⊗ (n u) (n v))]
    [(And u v)         (And (n u) (n v))]
    [(Or u v)          (Or (n u) (n v))]
    [(And u)           (And (n u))]
    [(Or u)            (Or  (n u))]
    [(Expt u v)        (Expt (n u) (n v))]
    [(Ln u)            (Ln   (n u))]
    [(Log u)           (Log  (n u))]
    [(Log u v)         (Log  (n u) (n v))]
    [(Sin u)           (Sin  (n u))]
    [(Asin u)          (Asin (n u))]
    [(Cos u)           (Cos  (n u))]
    [(Acos u)          (Acos (n u))]
    [(Factorial u)     (Factorial (n u))]
    [(Gamma u)         (Gamma (n u))]
    [(Prime? u)        (Prime? (n u))]
    [(Odd-prime? u)    (Odd-prime? (n u))]
    [(Nth-prime u)     (Nth-prime (n u))]
    [(Random-prime u)  (Random-prime (n u))]
    [(Next-prime u)    (Next-prime (n u))]
    [(Prev-prime u)    (Prev-prime (n u))]
    [(Divisors u)      (Divisors (n u))]
    [(app: f us) (match u
                   [(list '/ u v)  (⊘ (n u) (n v))]
                   [(list '- u)    (⊖ (n u))]
                   [(list '- u v)  (⊖ (n u) (n v))]
                   [(list 'tan v)  (Tan  (n v))]
                   [(list 'sqr u)  (Sqr  (n u))]
                   [(list 'sqrt u) (Sqrt (n u))]
                   [(list 'exp u)  (Exp  (n u))]  
                   [(list 'bf u) (number? u) (bf u)]
                   [(list* 'or us) (apply Or: us)]
                   [_ (let ([nus (map n us)])
                        (if (equal? us nus)
                            u
                            (n `(,f ,@nus))))])]))

(module+ test
  (check-equal? (normalize '(+ 1 x (* (expt (sin (ln (cos (asin (acos (sqrt (tan x))))))) 2))))
                (⊕ 1 x (⊗ (Expt (Sin (Ln (Cos (Asin (Acos (Sqrt (Tan x))))))) 2))))
  (check-equal? (normalize '(/ (- x) (+ (- x y) (exp x) (sqr x) (+ 3)))) 
                (⊘ (⊖ x) (⊕ (⊖ x y) (Exp x) (Sqr x) (⊕ 3))))
  (check-equal? (normalize '(bf 3)) (bf 3))
  (check-equal? (normalize '(f (- x y))) `(f ,(⊖ x y)))
  (check-equal? (normalize '(log 3)) '(log 10 3)))

; Compile turns an expression into a Racket function.
(define (compile u [x 'x])
  ; todo: check that x is the only free variable in u
  (eval `(λ (,x) ,u) (make-base-namespace)))

(module+ test (check-equal? ((compile '(sin (sqrt x))) 0) 0))


; distribute applies the distributive law recursively
(define (distribute s)
  ; (displayln (list 'distribute s))
  (define d distribute)
  (math-match s
    [(⊗ a (⊕ u v)) (⊕ (d (⊗ a u)) (d (⊗ a v)))]
    [(⊗ (⊕ u v) b) (⊕ (d (⊗ u b)) (d (⊗ v b)))]
    ; the following case handle a sum as a middle factor
    [(⊗ a b)       (let ([db (d b)])
                     (if (equal? b db) (⊗ a db) (d (⊗ a db))))]
    [(⊕ u v)       (⊕ (d u) (d v))]
    [_ s]))

(module+ test
  (check-equal? (distribute (⊗ 2 (⊕ 3 x y))) '(+ 6 (* 2 x) (* 2 y)))
  (check-equal? (distribute (⊗ (⊕ x y) (Cos x))) '(+ (* x (cos x)) (* y (cos x))))
  (check-equal? (distribute (⊗ (⊕ 3 x y) 2)) '(+ 6 (* 2 x) (* 2 y)))
  (check-equal? (distribute (⊕ 1 (⊗ 2 (⊕ 3 x y)))) '(+ 7 (* 2 x) (* 2 y)))
  (check-equal? (distribute '(* 2 x (+ 1 x))) (⊕ (⊗ 2 x) (⊗ 2 (Sqr x))))
  (check-equal? (distribute '(* (+ x 1) 2)) (⊕ (⊗ 2 x) 2)))

(define (expand u)
  ; expand products and powers with positive integer exponents
  ; expand terms, but don't recurse into sub terms
  ; TODO : implement the above description
  (expand-all u))

(define (expand-all u)
  ; expand products and powers with positive integer exponents, do recurse
  ; (displayln (list 'expand s))
  (define e expand-all)
  (define d distribute)
  (match u
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
                      (let ()
                        (define t (e (Expt (⊕ u v) (/ n 2))))
                        (e (⊗ t t)))]
    [(Expt (⊗ u v) w) (e (⊗ (Expt u w) (Expt v w)))]
    [(Ln (Expt u v))  (e (⊗ v (Ln (e u))))]
    [(Equal u v)      (Equal (e u) (e v))]
    [(Or u v)         (Or (e u) (e v))]
    [(And u v)        (And (e u) (e v))]
    [_ u]))

(module+ test
  (check-equal? (expand (Sqr (⊕ x y))) (⊕ (Sqr x) (Sqr y) (⊗ 2 x y)))
  (check-equal? (expand (Expt (⊕ x y) 4)) (expand (⊗ (Sqr (⊕ x y)) (Sqr (⊕ x y)))))
  (check-equal? (expand (⊗ (⊕ x y) (Cos x))) '(+ (* x (cos x)) (* y (cos x))))
  (check-equal? (expand (Ln (Expt x 3))) (⊗ 3 (Ln x)))
  (check-equal? (expand '(* 2 x (+ 1 x))) (⊕ (⊗ 2 x) (⊗ 2 (Sqr x))))
  (check-equal? (expand '(* (expt (+ 1 x) 2) (sin 2))) 
                '(+ (* 2 x (sin 2)) (* (expt x 2) (sin 2)) (sin 2))))

(define (simplify u)
  (define s simplify)
  (math-match u
    [(Expt n 1/2) (Expt n 1/2)]
    [(⊗ u v)      (⊗ (s u) (s v))]
    [(⊕ u v)      (⊕ (s u) (s v))]
    [_ u]))

(module+ test (check-equal? (simplify '(+ 3 (* 2 (expt 8 1/2)))) (⊕ (⊗ 2 2 (Sqrt 2)) 3)))

; divide u by v
(define (Oslash: u v)
  (math-match* (u v)
    [(r 0) +nan.0]
    [(r s) (/ r s)]
    [(u 1) u]
    [(u -1) (⊖ u)]
    [(u v) (⊗ u (Expt v -1))]))

(define-match-expander ⊘
  ; Note: This matches kind of quotient only
  (λ (stx) (syntax-parse stx [(_ u v) #'(or (list '* u (list 'expt v -1))
                                            (list '* (list 'expt v -1) u))]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Oslash: u v)] [_ (identifier? stx) #'Oslash:])))

(module+ test
  (check-equal? (math-match (⊘ x y) [(⊘ u v) (list u v)]) '(x y)))

(define (Quotient: u v)
  (⊘ u v))

(define-match-expander Quotient
  ; Note: This matches everything and writes it as a quotient
  (λ (stx) (syntax-parse stx [(_ u v) #'(and (app numerator u) (app denominator v))]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Quotient: u v)] [_ (identifier? stx) #'Quotient:])))

(module+ test
  (check-equal? (math-match 2/3 [(Quotient u v) (list u v)]) '(2 3))
  (check-equal? (math-match (⊘ x (⊗ 2 y z)) [(Quotient u v) (list u v)]) '(x (* 2 y z))))

(define (denominator u)
  (local-require (prefix-in racket: (only-in racket denominator)))
  (math-match u
    [p    1]
    [α (racket:denominator u)]
    [r.0  1]
    [r.bf (bf 1)]
    [x 1]
    [(Expt u r) #:when (negative? r) (Expt u (- r))]
    [(Expt u r) #:when (positive? r) 1]
    [(⊗ u v) (⊗ (denominator u) (denominator v))]
    [(⊕ u v) 1]
    [_ 1]))

(module+ test
  (check-equal? (denominator 2) 1)
  (check-equal? (denominator 2.1) 1)
  (check-equal? (denominator 0.5) 1)
  (check-equal? (denominator 2/3) 3)
  (check-equal? (denominator y) 1)
  (check-equal? (denominator (bf 1.2)) (bf 1)) ; xxx
  (check-equal? (denominator (Sqrt x)) 1)
  (check-equal? (denominator (⊘ 2 x)) x)
  (check-equal? (denominator (⊗ 3/5 (⊘ 2 x))) (⊗ 5 x)))

(define (numerator u)
  (local-require (prefix-in racket: (only-in racket numerator)))
  (math-match u
    [α (racket:numerator α)]
    [r r]
    [r.bf r.bf]
    [x x]
    [(⊗ u v) (⊗ (numerator u) (numerator v))]
    [(⊕ v w) u]
    [(Expt v r) #:when (positive? r) u]
    [(Expt v r) #:when (negative? r) 1]
    [_ u]))

(module+ test
  (check-equal? (numerator 2) 2)
  (check-equal? (numerator 2.1) 2.1)
  (check-equal? (numerator 2/3) 2)
  (check-equal? (numerator pi.bf) pi.bf)
  (check-equal? (numerator 'a) 'a)
  (check-equal? (numerator '(⊕ (⊘ 1 x) (⊘ 1 y))) '(⊕ (⊘ 1 x) (⊘ 1 y)))
  (check-equal? (numerator (⊘ 2 x)) 2)
  (check-equal? (numerator (⊗ 3/5 (⊘ 2 x))) (⊗ 3 2))
  (check-equal? (numerator (⊘ x y)) x))

(define (together u)
  ; todo : this doesn't handle sums with more than two terms
  (math-match u
    [(⊕ (⊘ u v) (⊘ a b)) (⊘ (⊕ (⊗ u b) (⊗ a v)) (⊗ v b))]
    [_ u]))

(module+ test 
  (check-equal? (denominator (together (normalize '(+ (/ a b) (/ c d))))) '(* b d))
  (check-equal? (numerator   (together (normalize '(+ (/ a b) (/ c d))))) '(+ (* a d) (* b c))))


; unary and binary minus 
(define (⊖ . us)
  (match us
    [(list u)   (⊗ -1 u)]
    [(list u v) (⊕ u (⊗ -1 v))]
    [_ (error)]))

;; The pattern Exp matches the natural exponential function
;;  (Exp u) matches (expt @e a) and binds u->a
;; The symbol @e is symbolic representation of Euler's constant.
;; In an expression context (Exp u) is `(expt @e ,u))
(define (Exp: u) (Expt @e u))

(define-match-expander Exp
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt @e u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Expt: @e u)] [_ (identifier? stx) #'Exp:])))

(define (Expt: u v)
  (define (sqrt-natural n)
    ; suppose n = s^2 * f , where f is square-free
    ; sqrt(n) = s * sqrt(f)
    (match n
      [0 0]
      [1 1]
      [_ (define-values (ss ns)
           (for/fold ([squares '()] [non-squares '()])
             ([b^e (in-list (factorize n))])
             (define-values (b e) (values (first b^e) (second b^e)))
             (if (even? e)
                 (values (cons (expt b (/ e 2)) squares) non-squares)
                 (values (cons (expt b (/ (- e 1) 2)) squares) (cons b non-squares)))))
         (⊗ (for/product ([s (in-list ss)]) s)
            (match (for/product ([n (in-list ns)]) n) 
              [1 1] [p `(expt ,p 1/2)]))]))
  (math-match* (u v)
    [(1 v)          1]
    [(u 1)          u]
    [(0 0)          +nan.0] ; TODO: is this the best we can do?
    [(u 0)          1]
    ; [(0 v)          0]
    [(n 1/2)        (sqrt-natural n)]
    [(α p)          (expt α p)]
    [(p q)          (expt p q)]
    [(r.0 s)        (expt r.0 s)] ; inexactness is contagious
    [(r s.0)        (expt r s.0)]
    [((⊗ u v) w)    (⊗ (Expt u w) (Expt v w))] ; xxx - only true for real u and v
    [((Expt u v) w) (Expt u (⊗ v w))]          ; ditto
    [(Exp (Ln v))   v]    
    [(_ _)          `(expt ,u ,v)]))

(define-match-expander Expt
  (λ (stx) (syntax-parse stx [(_ u v) #'(list 'expt u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Expt: u v)] [_ (identifier? stx) #'Expt:])))

(module+ test
  (check-equal? (Expt 2 3) 8)
  (check-equal? (Expt -1 2) 1)
  (check-equal? (bf-N '(expt (expt 5 1/2) 2)) (bf 5)))

(define (Sqr: u)
  (Expt u 2))

(define-match-expander Sqr
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqr: u)] [_ (identifier? stx) #'Sqr:])))

(define (Ln: u)
  (math-match u
    [1  0]
    ; [0  +nan.0] ; TODO: error?
    [r.0   #:when (positive? r.0)    (log r.0)]
    [r.bf  #:when (bfpositive? r.bf) (bflog r.bf)]
    [@e  1]
    [(Expt @e v) v]
    [_ `(ln ,u)]))

(define-match-expander Ln
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'ln u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Ln: u)] [_ (identifier? stx) #'Ln:])))

(module+ test
  (check-equal? (Ln 1)  0)
  (check-equal? (Ln 1.) 0.)
  (check-equal? (Ln (bf 1)) 0.bf)
  (check-equal? (Ln @e) 1)
  (check-equal? (Ln (Exp 1.0)) 1.0)
  (check-true   (bf<  (bfabs (bf- (bflog (bfexp (bf 1))) (bf 1)))  (bfexpt (bf 10) (bf -30))))
  (check-equal? (Ln (Exp x)) x)
  (check-equal? (Ln (Expt (Exp x) 2)) '(* 2 x))
  (check-equal? (Ln (Expt x 3)) '(ln (expt x 3))))


(define (fllog10 u [v #f])
  (math-match* (u v)
    [(_ #f)    (fllog10 10 u)]
    [(r.0 s.0) (fllogb r.0 s.0)]
    [(r.0 s)   (fllogb r.0 (exact->inexact s))]
    [(r   s.0) (fllogb (exact->inexact r) s.0)]
    [(r    s)  (fllogb (exact->inexact r) (exact->inexact s))]
    [(_ _)     (error 'fllog10 (~ "got: " u " and " v))]))

(module+ test
  (check-equal? (fllog10 1)  0.)
  (check-equal? (fllog10 1.) 0.)
  (check-equal? (fllog10 10.) 1.)
  (check-equal? (fllog10 100.) 2.)
  (check-equal? (fllog10 2. 8.) 3.)
  (check-equal? (fllog10 2. 16.) 4.))

(define (Log: u [v #f])
  (math-match* (u v)
    [(_ #f)    (Log: 10 u)] ; 10 is the default base
    [(@e v)    (Ln: v)]     ; special case the natural logarithm
    [(_ 1)     0]
    ; [(_ 0)     +nan.0] ; TODO: error?
    [(n m) #:when (divides? n m) (let ([k (max-dividing-power n m)])
                                   (⊕ k (Log n (⊘ m (Expt n k)))))]
    [(n m) `(log ,n ,m)]
    [(2 r)  (fllog2 r)]
    [(r s)  #:when (and (positive? r) (positive? s)) (fllog10 r s)]
    
    [(10   r.bf) #:when (bfpositive? r.bf)                          (bflog10 r.bf)]
    [(2    r.bf) #:when (bfpositive? r.bf)                          (bflog2  r.bf)]
    [(r.bf s.bf) #:when (and (bfpositive? r.bf) (bfpositive? s.bf)) (bf/ (bflog r.bf) (bflog s.bf))]
    [(r    s.bf)  (Log: (bf r) s.bf)]
    [(r.bf s)     (Log: r.bf  (bf s))]
    
    [(u u)          1]
    [(u (Expt u v)) v]
    
    ; [(n r.0) (log10 n r.0)]
    [(_ _)          `(log ,u ,v)]))

(define-match-expander Log
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'log u)] [(_ u v) #'(list 'log u v)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Log: u)] [(_ u v) #'(Log: u v)] [_ (identifier? stx) #'Log:])))

(module+ test
  (check-equal? (Log 2 1) 0)
  (check-equal? (Log 2 2) 1)
  (check-equal? (Log 2 4) 2)
  (check-equal? (Log 2 8) 3)
  (check-equal? (Log 2. 8.) 3.)
  (check-equal? (Log @e x) (Ln x))
  (check-equal? (Log 2 (Expt 2 x)) x))

(define (Cos: u)
  (math-match u
    [0 1]
    ; [r (cos r)] ; nope - automatic evaluation is for exact results only
    [r.0 (cos r.0)]
    [@pi -1]
    [(⊗ α u)   #:when (negative? α)      (Cos: (⊗ (- α) u))]  ; cos is even
    [(⊗ n @pi)                           (if (even? n) 1 -1)]    
    [(⊗ α @pi) #:when (integer? (* 2 α)) (cos-pi/2* (* 2 α))]
    #;[(⊗ α @pi) #:when (even? (denominator α)) ; half angle formula
                 (⊗ 'sign (Sqrt (⊗ 1/2 (⊕ 1 (Cos (⊗ 2 α @pi))))))] ; xxx find sign
    [(⊗ p (Integer _) @pi) #:when (even? p) 1]
    
    [(⊕ u (k⊗ p @pi)) #:when (odd? p)  (⊖ (Cos: u))]
    [(⊕ (k⊗ p @pi) u) #:when (odd? p)  (⊖ (Cos: u))]
    [(⊕ u (k⊗ p @pi)) #:when (even? p) (Cos: u)]
    [(⊕ (k⊗ p @pi) u) #:when (even? p) (Cos: u)]
    [(⊕ u (⊗ p (Integer _) @pi)) #:when (even? p) (Cos: u)]
    [(⊕ (⊗ p (Integer _) @pi) u) #:when (even? p) (Cos: u)]
    
    [(Acos u) u]    ; xxx only of -1<u<1 
    [_ `(cos ,u)]))

(define-match-expander Cos
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'cos u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Cos: u)] [_ (identifier? stx) #'Cos:])))

(module+ test
  (check-equal? (Cos 0) 1)
  (check-equal? (Cos @pi) -1)
  (check-equal? (Cos (⊗ 2 @pi)) 1)
  (check-equal? (Cos 0.5) 0.8775825618903728)
  (check-equal? (for/list ([n 8]) (Cos (⊗ n 1/2 @pi))) '(1 0 -1 0 1 0 -1 0))
  (check-equal? (Cos (⊖ x)) (Cos x))
  (check-equal? (Cos (⊕ x (⊗ 2 @pi)))  (Cos x))
  (check-equal? (Cos (⊕ x (⊗ 4 @pi)))  (Cos x))
  (check-equal? (Cos (⊕ x (⊗ -4 @pi))) (Cos x))
  (check-equal? (Cos (⊕ x @pi))        (⊖ (Cos x)))
  (check-equal? (Cos (⊕ x (⊗ 3 @pi)))  (⊖ (Cos x)))
  (check-equal? (Cos (⊕ x (⊗ 2 @n @pi))) (Cos x))
  (check-equal? (Cos (⊕ x (⊗ 4 @n @pi))) (Cos x))
  (check-equal? (Cos (⊕ x (⊗ 2 @p @pi))) (Cos x)))

(define (Sin: u)
  (define (Odd? n)  (and (integer? n) (odd? n)))
  (define (Even? n) (and (integer? n) (even? n)))
  (math-match u
    [0 0]
    [r.0 (sin r.0)]
    [@pi 0]
    [(⊗ (Integer _) @pi) 0]
    [(⊗ α     u) #:when (negative? α)      (⊖ (Sin: (⊗ (- α) u)))]
    [(⊗ α   @pi) #:when (integer? (* 2 α)) (if (= (remainder (* 2 α) 4) 1) 1 -1)]
    [(⊗ (Integer _) (Integer _) @pi) 0]
    [(⊕ u (k⊗ (Integer v) @pi)) #:when (Even? v) (Sin: u)]
    [(⊕ (k⊗ (Integer v) @pi) u) #:when (Even? v) (Sin: u)]
    [(⊕ u (k⊗ (Integer v) @pi)) #:when (Odd? v) (⊖ (Sin: u))]
    [(⊕ (k⊗ (Integer v) @pi) u) #:when (Odd? v) (⊖ (Sin: u))]
    [(⊕ u (⊗ p (Integer v) @pi)) #:when (Even? p) (Sin: u)]
    [(⊕ (⊗ p (Integer v) @pi) u) #:when (Even? p) (Sin: u)]
    [(⊕ u (⊗ p (Integer v) @pi)) #:when (Odd? p) (⊖ (Sin: u))]
    [(⊕ (⊗ p (Integer v) @pi) u) #:when (Odd? p) (⊖ (Sin: u))]
    #;[(⊗ α @pi) #:when (even? (denominator α)) ; half angle formula
                 (⊗ 'sign (Sqrt (⊗ 1/2 (⊖ 1 (Cos (⊗ 2 α @pi))))))] ; xxx find sign
    [(Asin u) u] ; only if -1<=u<=1   Maxima and MMA: sin(asin(3))=3 Nspire: error
    [_ `(sin ,u)]))

(define-match-expander Sin
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'sin u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sin: u)] [_ (identifier? stx) #'Sin:])))

(module+ test 
  (check-equal? (for/list ([n 8]) (Sin (⊗ n 1/2 @pi))) '(0 1 0 -1 0 1 0 -1))
  (check-equal? (Sin (⊖ x))              (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 2 @pi)))       (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 4 @pi)))       (Sin x))
  (check-equal? (Sin (⊕ x (⊗ -4 @pi)))      (Sin x))
  (check-equal? (Sin (⊕ x       @pi))    (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 3 @pi)))    (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 2 @n @pi)))    (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 4 @n @pi)))    (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 2 @p @pi)))    (Sin x)))

(define (Asin: u)
  (math-match u
    [0 0]
    [1  (⊗ 1/2 @pi)]
    [-1 (⊗ -1/2 @pi)]
    ; [r (sin r)] ; nope - automatic evaluation is for exact results only
    [r.0 (asin r.0)]
    [_ `(asin ,u)]))

(define-match-expander Asin
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'asin u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Asin: u)] [_ (identifier? stx) #'Asin:])))

(define (Acos: u)
  (math-match u
    [0 (⊘ @pi 2)]
    [1 0]
    [-1 @pi]
    [r.0 (acos r.0)]
    [_ `(acos ,u)]))

(define-match-expander Acos
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'acos u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Acos: u)] [_ (identifier? stx) #'Acos:])))

(define (Tan u)
  (⊘ (Sin u) (Cos u)))

(define (Degree u)
  (⊗ (⊘ @pi 180) u))

(define (Sqrt u)
  (Expt u 1/2))

(module+ test (check-equal? (Sqrt 0) 0) (check-equal? (Sqrt 1) 1) (check-equal? (Sqrt 4) 2))

(define (diff u x)
  (define (d u) (diff u x))
  (math-match u
    [r 0]
    [y #:when (eq? x y) 1]
    [y 0]
    [(⊕ v w)     (⊕ (d v) (d w))]
    [(⊗ v w)     (⊕ (⊗ (d v) w) (⊗ v (d w)))]
    [(Expt u r)  (⊗ r (Expt u (- r 1)) (d u))]
    [(Expt @e u) (⊗ (Exp u) (d u))]
    [(Expt u v)  (diff (Exp (⊗ v (Ln u))) x)] ; assumes u positive    
    ; [(Exp u)   (⊗ (Exp u) (d u))]
    [(Ln u)    (⊗ (⊘ 1 u) (d u))]
    [(Cos u)   (⊗ (⊖ 0 (Sin u)) (d u))]
    [(Sin u)   (⊗ (Cos u) (d u))]
    [(app: f us)  #:when (symbol? f) 
                  (match us
                    [(list u) (⊗ `((D ,f ,x) ,u) (d u))] ; xxx
                    [_ `(diff (,f ,@us) ,x)])]             ; xxx
    [_ (error 'diff (~a "got: " u " wrt " x))]))

(module+ test
  (check-equal? (diff 1 x) 0)
  (check-equal? (diff x x) 1)
  (check-equal? (diff y x) 0)
  (check-equal? (diff (⊗ x x) x) '(* 2 x))
  (check-equal? (diff (⊗ x x x) x) '(* 3 (expt x 2)))
  (check-equal? (diff (⊗ x x x x) x) '(* 4 (expt x 3)))
  (check-equal? (diff (⊕ (⊗ 5 x) (⊗ x x)) x) '(+ 5 (* 2 x)))
  (check-equal? (diff (Exp x) x) (Exp x))
  (check-equal? (diff (Exp (⊗ x x)) x) (⊗ 2 x (Exp (⊗ x x))))
  (check-equal? (diff (Expt x 1) x) 1)
  (check-equal? (diff (Expt x 2) x) (⊗ 2 x))
  (check-equal? (diff (Expt x 3) x) (⊗ 3 (Expt x 2)))
  (check-equal? (diff (Ln x) x) (⊘ 1 x))
  (check-equal? (diff (Ln (⊗ x x)) x) (⊘ (⊗ 2 x) (⊗ x x)))
  (check-equal? (diff (Cos x) x) (⊖ (Sin x)))
  (check-equal? (diff (Cos (⊗ x x)) x) (⊗ (⊖ (Sin (⊗ x x))) 2 x))
  (check-equal? (diff (Sin x) x) (Cos x))
  (check-equal? (diff (Sin (⊗ x x)) x) (⊗ 2 (Cos (Expt x 2)) x))
  ; TODO: ASE should rewrit the result to (* '(expt x x) (+ 1 (ln x)))
  (check-equal? (diff (Expt x x) x) '(* (expt @e (* x (ln x))) (+ 1 (ln x))))
  )

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
        [(Sin u) (Sin (l u))]
        [(Cos u) (Cos (l u))]
        [(Ln u)  (Ln  (l u))]
        [_ `(limit ,u ,x ,x0)]))
    (l u)))

(module+ test
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

;;; Substition

(define (subst u v w) ; substitue w for v in u
  (define (s u)
    (math-match u
      [u #:when (equal? u v) w]
      [(⊕ u1 u2)    (⊕ (s u1) (s u2))]
      [(⊗ u1 u2)    (⊗ (s u1) (s u2))]
      [(Expt u1 u2) (Expt (s u1) (s u2))]
      [(app: f us)   `(,f ,@(map s us))]
      [_ u]))
  (normalize (s u)))

(module+ test
  (check-equal? (subst '(expt (+ (* x y) 1) 3) y 1) '(expt (+ 1 x) 3))
  (check-equal? (let () (define (f x) '(expt (+ x 1) 3)) (subst (f x) x 1)) 8))

(define (subst* u vs ws)
  (for/fold ([u u]) ([v vs] [w ws])
    (subst u v w)))

(module+ test (check-equal? (subst* '(+ 1 x y z) '(x y) '(a b)) '(+ 1 a b z)))

;;; Numeric evalution

(define euler-e (exp 1))
; Given an expression without variables, N will evalutate the expression
; using Racket's standard mathematical operations.
(define (N u)
  (define (M  f F u)   (math-match (N u) [r (f r)] [v (F v)]))
  (define (M2 f F u v) (math-match* ((N u) (N v)) [(r s) (f r s)] [(v w) (F v w)]))
  (math-match u
    [r   r]
    [@pi pi]
    [@e  euler-e]
    [(⊕ u v)     (M2 + ⊕ u v)]
    [(⊗ u v)     (M2 * ⊗ u v)]
    [(Expt u v)  (M2 expt Expt u v)]
    [(Sin u)     (M sin Sin u)]
    [(Cos u)     (M cos Cos u)]
    [(Ln u)      (M log Ln  u)]
    [(Log u)     (M  fllog10 Log u)]
    [(Log u v)   (M2 fllog10 Log u v)]
    [(Exp u)     (M exp Exp u)]
    [(Asin u)    (M asin Asin u)]
    [(Acos u)    (M acos Acos u)]
    ; [(Atan u)    (M atan Atan u)]
    [(Equal u v) (M2 = Equal u v)]
    [(app: f us) `(,f ,@(map N us))]
    [_ u]))

(module+ test 
  (check-equal? (N (subst '(expt (+ x 1) 5) x @pi)) (expt (+ pi 1) 5))
  (check-equal? (N (normalize '(= x (sqrt 2)))) (Equal x (sqrt 2))))

(require math/bigfloat)
(bf-precision 100)
; Given an expression without variables, N will evalutate the expression
; using bigfloats. The optional argument can be used to temporarily change
; the precision. Set bf-precision for a global change of precision.
; The two last optional arguments can be used to substitute the variable x
; with a bigfloat value x0.bf. 
; Note: This is a temporary workaround until bigfloats are better supported.
(define (bf-N u [prec #f] [x #f] [x0.bf #f])
  (parameterize ([bf-precision (or prec (bf-precision))])
    (define e.bf (bfexp 1.bf))
    (define (N u)
      (define (M  f F u) (match (N u) [r #:when (bigfloat? r) (f r)] [v (F v)]))
      (define (M2 f F u v) 
        (match* ((N u) (N v)) 
          [(r s) #:when (and (bigfloat? r) (bigfloat? s)) (f r s)]
          [(v w) (F v w)]))
      (math-match u
        [r   (bf r)]
        [y #:when (eq? y x) x0.bf]
        [@pi pi.bf]
        [@e  e.bf]
        [(⊕ u v)     (M2 bf+ ⊕ u v)]
        [(⊗ u v)     (M2 bf* ⊗ u v)]
        [(Expt u v)  (M2 bfexpt Expt u v)]
        [(Sin u)     (M bfsin Sin u)]
        [(Cos u)     (M bfcos Cos u)]
        [(Ln u)      (M bflog Ln  u)]
        [(Exp u)     (M bfexp Exp u)]
        [(Asin u)    (M bfasin Asin u)]
        [(Acos u)    (M bfacos Acos u)]
        ; [(Atan u)    (M bfatan Atan u)]
        [(app: f us) (displayln (list 'bf-N f us))
                     `(,f ,@(map N us))]
        [_ u]))
    (N u)))



(define (taylor u x a n)
  (define (fact n) (if (<= n 0) 1 (* n (fact (- n 1)))))
  (define (terms u i)
    (cond [(> i n) 0]
          [else    (⊕ (⊗ (/ (fact i)) (subst u x a) (Expt (⊖ x a) i))
                      (terms (diff u x) (+ i 1)))]))
  (terms u 0))

(module+ test
  (check-equal? (taylor '(sin x) x 0 5) '(+ x (* -1/6(expt x 3)) (* 1/120 (expt x 5))))
  #;(check-equal? (N (expand (taylor '(sin x) x 2 3)))
                  '(+ -0.6318662024609201 (* 2.2347416901985055 x) 
                      (* -0.8707955499599833 (expt x 2)) (* 0.0693578060911904 (expt x 3)))))

(define (free-of u v)
  ; return true if is not a complete subexpression of u, false otherwise
  (define (f u)
    (and (not (equal? u v))
         (math-match u
           [r #t]
           [r.bf #t]
           [x #t]
           [(app: _ us) (andmap f us)])))
  (f u))

(module+ test
  (let () (define u (Expt (⊕ x 1) 2))
    (check-equal? (free-of u x) #f)
    (check-false (or  (free-of u x) (free-of u 1) (free-of u 2) (free-of u (⊕ x 1))))
    (check-true  (and (free-of u y) (free-of u 3) (free-of u (⊕ x 2))))))



(define sin-pi/2-table #(0 1 0 -1))
(define (sin-pi/2* n) (vector-ref sin-pi/2-table (remainder n 4)))
(define cos-pi/2-table #(1 0 -1 0))
(define (cos-pi/2* n) (vector-ref cos-pi/2-table (remainder n 4)))

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
                               (Expt (Cos x) k)
                               (Expt (Sin x) (- n k))
                               (sin-pi/2* (- n k))))]
      [(Cos 0) 1]
      [(Cos (⊗ n u)) #:when (negative? n)
                     (t (Cos (- n) u))]
      [(Cos (⊗ n u)) (for/⊕ ([k (in-range (+ n 1))])
                            (⊗ (binomial n k)
                               (Expt (Cos x) k)
                               (Expt (Sin x) (- n k))
                               (cos-pi/2* (- n k))))]
      [(Sin (⊕ u v)) (t (⊕ (⊗ (Sin u) (Cos v))  (⊗ (Sin v) (Cos u))))]
      [(Cos (⊕ u v)) (t (⊖ (⊗ (Cos u) (Cos v))  (⊗ (Sin u) (Sin v))))]
      [(Expt u n)  (expand (Expt (t u) n))]
      [(app: f us) `(,f ,@(map t us))]
      [_ u]))
  (t u))

(module+ test
  (check-equal? (trig-expand (Sin (⊗ 2 x))) (⊗ 2 (Cos x) (Sin x)))
  (check-equal? (trig-expand (Cos (⊗ 2 x))) (⊖ (Sqr (Cos x)) (Sqr (Sin x))))
  (let ([u 'u] [v 'v])
    (check-equal? (trig-expand (Sin (⊕ u v))) (⊕ (⊗ (Sin u) (Cos v))  (⊗ (Sin v) (Cos u))))
    (check-equal? (trig-expand (Cos (⊕ u v))) (⊖ (⊗ (Cos u) (Cos v))  (⊗ (Sin u) (Sin v))))
    (check-equal? (trig-expand '(expt (sin (* 2 x)) 2)) '(* 4 (expt (cos x) 2) (expt (sin x) 2)))))

(define-syntax (for/⊕ stx)
  (syntax-case stx ()
    [(_ clauses body-or-break ... body)
     (syntax/loc stx
       (for/fold ([sum 0]) clauses
         body-or-break ...
         (⊕ body sum)))]))

(module+ test (check-equal? (for/⊕ ([n 10]) (⊗ n x)) (⊗ (for/sum ([n 10]) n) x)))

(define-syntax (for/⊗ stx)
  (syntax-case stx ()
    [(_ clauses body-or-break ... body)
     (syntax/loc stx
       (for/fold ([prod 1]) clauses
         body-or-break ...
         (⊗ body prod)))]))

(module+ test (check-equal? (for/⊗ ([n (in-range 2 5)]) n) 24))

(define (exponent u w)
  ; find the maximum exponent of w which is present in u
  (define (e u)
    (math-match u
      [0 -inf.0]
      [u #:when (equal? u w) 1]
      [r 0]
      [r.bf 0]
      [x 0]
      [(⊕ u v) (max (e u) (e v))]
      [(⊗ u v) (+ (e u) (e v))]
      [(Expt u r) #:when (equal? u w) r]
      [(Expt (⊕ u v) r) (* (max (e u) (e v)) r)]
      [_ 0]))
  (e u))

(module+ test 
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
  (define (c u)
    (math-match u
      [r                            (if (= n 0) r    0)]
      [r.bf                         (if (= n 0) r.bf 0)]
      [u #:when (equal? u v)        (if (= n 1) 1 0)]
      [y #:when (not (equal? u v))  (if (= n 0) y 0)]
      [(⊗ r w)                      (⊗ r (c w))]
      [(⊗ u w) #:when (equal? u v)  (coefficient w v (- n 1))]
      [(⊗ u w) #:when (equal? w v)  (coefficient u v (- n 1))]
      [(⊗ u w)                      (for/⊕ ([i (in-range (+ n 1))])
                                           (⊗ (coefficient u v i) (coefficient w v (- n i))))]
      [(⊕ u w)                      (⊕ (c u) (c w))]
      [(Expt u r) #:when (equal? u v) (if (= r n) 1 0)]
      [(Expt (⊕ u w) m)             (for/⊕ ([i (in-range (+ m 1))])
                                           (⊗ (binomial m i)
                                              (coefficient (⊗ (Expt u i) (Expt w (- m i))) v n)))]
      [u                            (if (= n 0) u 0)]))
  (c u))

(module+ test 
  (let () (define u (normalize '(+ (* 3 (expt x 2) y z) x (* 2 (expt x 2)))))
    (check-equal? (coefficient u (Expt x 2)) '(+ 2 (* 3 y z)))
    (check-equal? (coefficient u x 2) '(+ 2 (* 3 y z)))
    (check-equal? (coefficient u x) 1)
    (check-equal? (coefficient '(expt (+ x 1) 2) x) 2)
    (check-equal? (coefficient '(* (expt a -1) x)  x) '(expt a -1))
    (check-equal? (coefficient (normalize '(+ 1 x (sqr x) (sin x))) x 0) '(+ 1 (sin x)))
    (check-equal? (coefficient (⊘ 3 x) x 1) 0)
    (check-equal? (coefficient (⊘ 3 x) x -1) 3)))

; (polynomial? u x)  is u a univariate polynomial in x ?
(define (polynomial? u x)
  (free-of (coefficient u x 0) x))

(module+ test
  (check-equal? (polynomial? '(/ z x) x) #f)
  (check-true 
   (andmap (curryr polynomial? x) 
           (list 0 x '(expt x 2) '(* 3 (expt x 4)) '(expt (+ 1 x) 3)
                 (⊕ (⊘ 3 y) (Expt x 2))))))

(define (coefficient-list u x)
  ; view u as a polynomial in x, return the list of coefficients
  ; use same interpretation as  coefficient  for terms not in the form c*x^n
  (match (for/list ([n (in-range (+ (exponent u x) 1))]) (coefficient u x n))
    [(list 0) '()] [cs cs]))

(module+ test 
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
  (check-equal? (is-power-of? '(expt x 3) x) #t)
  (check-equal? (is-power-of? '(expt y 3) x) #f)
  (check-equal? (is-power-of? '(sin x) x) #f))

(define (in-terms/proc u)
  (match u
    [(⊕ u v) (cons u (in-terms/proc v))]
    [u       (list u)]))

(module+ test 
  (check-equal? (in-terms/proc (normalize '(+ 1 2 x y (expt x 4) (sin x)))) 
                '(3 x (expt x 4) y (sin x))))

(define (part u . ns)
  ; as in Maxima http://maxima.sourceforge.net/docs/manual/en/maxima_6.html#IDX225 
  ; or perhaps I should write as in Maxima's inpart.
  (define (pick u ns)
    (match ns
      [(list) u]
      [(list* n ns) (pick (list-ref u n) ns)]))
  (pick u ns))

(module+ test 
  (check-equal? (part (⊕ 1 x y) 0) '+)
  (check-equal? (part (⊕ 1 x y) 1) 1)
  (check-equal? (part (⊕ 1 x y) 2) x)
  (check-equal? (part (⊕ 1 x y) 3) y)
  (check-equal? (part (⊕ 1 (⊗ 2 x) y) 2 2) x)
  (check-equal? (part (⊕ 1 (⊗ 2 x) y) 2 1) 2))


#;(define (polynomial? u v)
    ; is u a polynomial in v ?
    ...)


(define (leading-coefficient u x)
  (coefficient u x (exponent u x)))

(module+ test (check-equal? (leading-coefficient '(+ 2 (* 3 x) (* 17 x x)) x) 17))

(define (leading-term u x)
  (define n (exponent u x))
  (⊗ (coefficient u x n) (Expt x n)))

(module+ test (check-equal? (leading-term '(+ 2 (* 3 x) (* 17 x x)) x) (⊗ 17 x x)))

(define (variables u)
  ; find variables in sums, producs and powers with rational exponents
  (define (vars u vs)
    (math-match u
      [r          vs]
      [r.bf       vs]
      [x          (set-add vs x)]
      [(⊗ u v)   (vars u (vars v vs))]
      [(⊕ u v)   (vars u (vars v vs))]
      [(Expt u α) (vars u vs)]
      [else       vs]))
  (sort (set->list (vars u (set))) <<))

(module+ test (check-equal? (variables '(+ (expt (+ x y) 3) z (* a b c) (sin u))) '(a b c x y z)))

(define (collect u x)
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
  (let ([a 'a] [b 'b]) 
    (check-equal? (polynomial-quotient (Sqr x) (⊕ x a) x) (⊕ (⊖ a) x))
    (check-equal? (polynomial-quotient-remainder '(+ (* x x) x 1) '(+ (* 2 x) 1) x)
                  (list (⊕ 1/4 (⊘ x 2)) 3/4))
    (check-equal? (polynomial-quotient (⊕ (⊗ x x) (⊗ b x) 1) (⊕ (⊗ a x) 1) x)
                  '(+ (* -1 (expt a -2)) (* (expt a -1) b) (* (expt a -1) x)))))

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
  (check-equal? 
   (polynomial-square-free-factor (expand '(* (+ x -1) (expt (+ x 1) 2) (expt (+ x 2) 5))) x)
   (⊗ (Expt (⊕ 1 x) 2) (Expt (⊕ 2 x) 5) (⊕ -1 x)))
  (let ([u (⊕ (⊗ x x x x x) (⊗ 6 x x x x) (⊗ 10 x x x) (⊗ -4 x x) (⊗ -24 x) -16)])
    (check-equal? (polynomial-square-free-factor u x) '(* (expt (+ 2 x) 3) (+ -2 (expt x 2))))))

;;;
;;;
;;;

(define-match-expander Equal
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Equal: u v)] [_ (identifier? stx) #'Equal:])))

(define (Equal: u v)
  `(= ,u ,v))

(define-match-expander Or
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'or u v) (list-rest 'or u (app (λ(ys) (cons 'or ys)) v)))]
      [(_ u)       #'(list 'or u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(Or: u ...)] [_ (identifier? stx) #'Or:])))

(define (Or: . us)
  (define (flatten us)
    (reverse 
     (for/fold ([vs '()]) ([u (in-list us)])
       (match u
         [(list* 'or ws) (append vs (map flatten ws))]
         [_              (cons u vs)]))))
  `(or ,@(sort (flatten us) <<)))

(module+ test 
  (check-equal? (normalize '(or (= x 3) (or (= x 2) (= x 1)))) '(or (= x 1) (= x 2) (= x 3))))

(define-match-expander And
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'and u v) (list-rest 'and u (app (λ(ys) (cons 'and ys)) v)))]
      [(_ u)       #'(list 'and u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(And: u ...)] [_ (identifier? stx) #'And:])))

(define (And: . us)
  (define (flatten us)
    (reverse 
     (for/fold ([vs '()]) ([u (in-list us)])
       (match u
         [(list* 'and ws) (append vs (map flatten ws))]
         [_               (cons u vs)]))))
  `(and ,@(sort (flatten us) <<)))

(module+ test 
  (check-equal? (normalize '(and (= x 3) (and (= x 2) (= x 1)))) '(and (= x 1) (= x 2) (= x 3))))

#;(define (Positive?: u)
    (math-match u
      [r      (positive? r)]
      [r.bf   (bfpositive? r.bf)]
      [(⊖ u)  #f]
      [_      #t])) ; todo: add cases for variables with assumptions

(define (solve eqn x) ; assume x is real (use csolve for complex solutions)
  (let/ec return
    (define (solve-by-inverse w)
      (define (remove-invertibles w)
        ; Input:  w = (Equal u v) where v is free of x
        ; Output: If w=f(u) then (remove-invertibles u (f^-1 v))
        ;         otherwise w.
        (define r remove-invertibles)
        (math-match w
          [(Equal (⊕ w u) v)     #:when (free-of w x) (r (Equal u (⊖ v w)))]
          [(Equal (⊕ u w) v)     #:when (free-of w x) (r (Equal u (⊖ v w)))]
          [(Equal (⊗ w u) v)     #:when (free-of w x) (r (Equal u (⊘ v w)))]
          [(Equal (⊗ u w) v)     #:when (free-of w x) (r (Equal u (⊘ v w)))]
          [(Equal (Expt @e u) s) #:when (> s 0)        (r (Equal u (Ln s)))]
          [(Equal (Expt @e u) s) (return #f)]
          [(Equal (Expt @e u) v) (r (Equal u (Ln v)))]  ; xxx TODO message: only correct if v>0 
          [(Equal (Expt u n) v)  #:when (odd? n)  (r (Equal u (Expt v (⊘ 1 n))))]
          [(Equal (Expt u -1) v) (r (Equal u (Expt v -1)))] ; assumes v<>0 (as does MMA)
          [(Equal (Expt u α) v)  #:when (= (numerator α) 1)           (r (Equal u (Expt v (⊘ 1 α))))]
          [(Equal (Expt n u) m)  #:when (and (free-of n x) (free-of m x)) (r (Equal u (Log n m)))]
          [(Equal (Expt v u) w)  #:when (and (free-of v x) (free-of w x)) 
                                 (r (Equal u (Log v w)))]          
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
      (match eqn
        ; rewrite u=v to u-v=0
        [(Equal u v) #:when (not (equal? v 0)) (solve1 (Equal (⊖ u v) 0))]
        ; rule of zero product
        [(Equal (⊗ u v) 0)    (Or (solve (Equal u 0) x) (solve1 (Equal v 0)))]
        [(Equal (Expt u r) 0) (solve1 (Equal u 0))]
        [(Equal u 0) 
         (match (coefficient-list u x) ; note: leading coef is non-zero
           [(list)       #t]
           [(list a)     (Equal a 0)]             ; zero order
           [(list b a)   (Equal x (⊘ (⊖ b) a))]  ; first order
           ; second order
           [(list 0 0 a) (Equal x 0)]
           [(list 0 b a) (Or (Equal x 0) (Equal x (⊖ (⊘ b a))))]
           [(list c 0 a) (Or (Equal x (⊖ (Sqrt (⊘ (⊖ c) a))))
                             (Equal x    (Sqrt (⊘ (⊖ c) a))))]
           [(list c b a) (define sqrt-d (Sqrt (⊖ (Sqr b) (⊗ 4 a c))))
                         (Or (Equal x (distribute (⊘ (⊖ (⊖ b) sqrt-d) (⊗ 2 a))))
                             (Equal x (distribute (⊘ (⊕ (⊖ b) sqrt-d) (⊗ 2 a)))))]       
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
  (check-equal? (solve '(= 8 (expt 2 x)) x) '(= x 3)))


(define (roots u x)
  (define (solution u) (last u))
  (define (extract u)
    (match u
      [(list 'or e ...) (map solution e)]
      [(list _ '= x0)   (list x0)]
      [_                '()]))
  (extract (solve (Equal u 0) x)))

; > (let () ; Example: The discriminant of a second degree polynomial
;     (match-define (list x1 x2) (roots '(+ (* x x) (* b x) c) x))
;     (expand (Sqr (⊖ x1 x2))))
; '(+ (expt b 2) (* -4 c))

; Example: Calculate the Taylor series of sin around x=2 up to degree 11.
;          Use 100 bits precision and evaluate for x=2.1
; > (bf-N (taylor '(sin x) x 2 11) 100 x (bf 2.1))
; (bf #e0.86320936664887372583952624450375)
;; Let us compare this to normal precision sin in 2.1
; > (sin 2.1)
;       0.8632093666488738
;; How many digits are correct?
; > (bf- (bf-N (taylor '(sin x) x 2 11) 100 x (bf 2.1))
;        (bfsin (bf 2.1)))
; (bf #e-1.8915312386301848139346245961623e-21)
; Twenty digits!

(define (newton-raphson f x u0 [n 10] #:trace? [trace? #f])
  ; Use Newton-Raphson's metod to solve the equation f(x)=0.
  ; The starting point is u0. The number of iterations is n.
  (define df (diff f x))
  (define g (normalize `(- x (/ ,f ,df))))
  (for/fold ([xn (N u0)]) ([n n])
    (when trace? (displayln (list n xn)))
    (subst g x xn)))

(define (bf-newton-raphson f x u0 [n 10] #:precision [prec 100] #:trace? [trace? #f])
  ; Use Newton-Raphson's metod to solve the equation f(x)=0.
  ; The starting point is u0. The number of iterations is n.
  ; Precision is the number of bits used in the big float compuations.
  (define df (diff f x))
  (define g (normalize `(- x (/ ,f ,df))))
  (for/fold ([xn (bf-N u0 prec)]) ([n n])
    (when trace? (displayln (list n xn)))
    (bf-N g prec x xn)))

; (bf-newton-raphson '(- (sin x) 1.0) x 1. 80 #:trace? #t)

;;;
;;; Display
;;;

(define (default-output-log u [v #f])
  (match-define (list l r) (output-application-brackets))
  (cond [v    (~a "log_" (verbose~ u) l (verbose~ v) r)]
        [else (~a "log" l (verbose~ u) r)]))

(define output-application-brackets   (make-parameter (list "(" ")")))
(define output-format-function-symbol (make-parameter ~a))
(define output-format-quotient        (make-parameter #f)) ; #f means default u/v
(define output-sub-expression-parens  (make-parameter (list "(" ")")))
(define output-wrapper                (make-parameter values))
(define output-use-quotients?         (make-parameter #t))
(define output-format-sqrt            (make-parameter (λ(u)   (~a "sqrt(" (verbose~ u) ")"))))
(define output-format-log             (make-parameter default-output-log))

(define (use-mma-output-style)
  (output-application-brackets (list "[" "]"))
  (output-format-function-symbol (λ(s) (string-titlecase (~a s))))
  (output-format-quotient #f)
  (output-sub-expression-parens (list "(" ")"))
  (output-wrapper values)
  (output-format-sqrt (λ(u) (~a "Sqrt[" (verbose~ u) "]")))
  (output-format-log default-output-log))

(define (use-default-output-style)
  (output-application-brackets (list "(" ")"))
  (output-format-function-symbol ~a)
  (output-format-quotient #f)
  (output-sub-expression-parens (list "(" ")"))
  (output-wrapper values)
  (output-format-sqrt (λ(u) (~a "sqrt(" (verbose~ u) ")")))
  (output-format-log default-output-log))

(define (use-tex-output-style)
  (define operators '(sin cos tan asin acos atan log ln))
  (define (~symbol s) 
    (match s
      [_ #:when (member s operators) (~a "\\" s)]
      ['*   "\\cdot "]
      ['or  "\\vee "]
      ['and "\\wedge "]
      [_  (~a s)]))
  (output-application-brackets (list "(" ")"))
  (output-format-function-symbol ~symbol)
  (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
  (output-sub-expression-parens (list "{" "}"))
  (output-wrapper (λ (s) (~a "$" s "$")))
  (output-format-sqrt (λ(u) (parameterize ([output-wrapper values])
                              (~a "\\sqrt{" (verbose~ u) "}"))))
  (output-format-log 
   (λ (u [v #f])
     (parameterize ([output-wrapper values])
       (cond [v    (~a "log_{" (verbose~ u) "}(" (verbose~ v) ")")]
             [else (~a "log(" (verbose~ u) ")")])))))

(define (tex u)
  (define operators '(sin cos tan asin acos atan log ln))
  (define (~symbol s) 
    (match s
      [_ #:when (member s operators) (~a "\\" s)]
      ['* "\\cdot "]
      ['or "\\vee "]
      ['and "\\wedge "]
      [_  (~a s)]))
  (parameterize ((output-application-brackets (list "(" ")"))
                 (output-format-function-symbol ~symbol)
                 (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
                 (output-sub-expression-parens (list "{" "}"))
                 (output-wrapper (λ (s) (~a "$" s "$")))
                 (output-format-sqrt (λ(u) (parameterize ([output-wrapper values])
                                             (~a "\\sqrt{" (verbose~ u) "}"))))
                 (output-format-log
                  (parameterize ([output-wrapper values])
                    (λ (u [v #f])
                      (cond [v    (~a "log_{" (verbose~ u) "}(" (verbose~ v) ")")]
                            [else (~a "log(" (verbose~ u) ")")])))))
    (verbose~ u)))

; ~ converts an expression into a string
(define (verbose~ u)
  (match-define (list app-left app-right) (output-application-brackets))
  (match-define (list sub-left sub-right) (output-sub-expression-parens))
  (define use-quotients? (output-use-quotients?))
  (define ~sym (output-format-function-symbol))
  (define (v~ u)
    (define (sub u) ; always wrap in sub-left and sub-right parentheses
      (~a sub-left (v~ u) sub-right))
    (define (paren u) ; always wrap in ( )
      (~a "(" (v~ u) ")"))
    (define (par u #:use [wrap paren]) ; wrap if (locally) necessary
      (math-match u
        [r    #:when (>= r 0)           (~a r)]
        [r.bf #:when (bf>= r.bf (bf 0)) (~a r.bf)]
        [x (~a x)]
        ; infix operators and relations
        [(⊗ u v)     (~a (par u) (~sym '*) (par v))]
        [(⊕ _ __)    (paren u)]
        [(And u v)   (~a (par u) " " (~sym 'and) " " (par v))]
        [(Or u v)    (~a (par u) " " (~sym 'or)  " " (par v))]
        [(Equal u v) (~a (par u) " " (~sym '=)   " " (par v))]
        ; powers
        [(Expt u 1/2) ((output-format-sqrt) u)]
        [(Expt u p)   (~a (par u) (~sym '^) (par p #:use sub))]
        [(Expt u v)   (~a (par u) (~sym '^) (wrap v))]
        [(Log u)      ((output-format-log) u)]
        [(Log u v)    ((output-format-log) u v)]
        ; applications
        [(app: f us) (let ()
                       (define arguments (apply string-append (add-between (map v~ us) ",")))
                       (define head ((output-format-function-symbol) f))
                       (~a head app-left arguments app-right))]
        [_  (wrap u)]))
    (math-match u
      [r           (~a r)]
      [r.bf        (bigfloat->string r.bf)]
      [x           (~a x)]
      [(Quotient u v) #:when (and use-quotients? (not (rational? v)))
                      (define format/ 
                        (or (output-format-quotient)
                            (λ (u v) (~a u "/" v))))
                      (format/ (par u #:use sub) (par v #:use sub))]
      [(⊗ u v)     (~a (par u) (~sym '*) (par v))]
      [(⊕ u v)     (~a (v~ u) (~sym '+) (v~ v))]
      [(And u v)   (~a (par u) " " (~sym 'and) " " (par v))]
      [(Or u v)    (~a (par u) " " (~sym 'or)  " " (par v))]
      [(Equal u v) (~a (par u) " " (~sym '=)   " " (par v))]
      ; [(⊖ u v)     (~a (par u) "-" (v~ v))]
      ; [(⊘ u v)     (~a (par u) (~sym '/) (par v))]
      [(Expt u 1/2) ((output-format-sqrt) u)]
      [(Expt u v)  (~a (par u) (~sym '^) (par v #:use sub))]
      [(Equal u v) (~a (v~ u) (~sym '=) (v~ v))]
      [(Log u)     ((output-format-log) u)]
      [(Log u v)   ((output-format-log) u v)]
      [(app: f us) (let ()
                     (define arguments (apply string-append (add-between (map v~ us) ",")))
                     (define head ((output-format-function-symbol) f))
                     (~a head app-left arguments app-right))]
      [_ (display u)
         (error 'verbose~ (~a "internal error, got: " u))]))
  ((output-wrapper) (v~ u)))

(define ~ verbose~)

(module+ test
  (check-equal? (verbose~ (expand (Expt (⊕ x 1) 3))) "1+3*x+3*x^2+x^3")
  (check-equal? (verbose~ (Sin (⊕ x -7))) "sin(-7+x)")
  (check-equal? (verbose~ (normalize '(* (sin (+ x -7)) (+ (cos (+ x -7)) (asin (+ x -7))))))
                "sin(-7+x)*(asin(-7+x)+cos(-7+x))")
  (check-equal? (parameterize ([bf-precision 100]) (verbose~ pi.bf))
                "3.1415926535897932384626433832793")
  (use-mma-output-style)
  (check-equal? (verbose~ (Sin (⊕ x -7))) "Sin[-7+x]")
  (use-default-output-style)
  (check-equal? (verbose~ (Sin (⊕ x -7))) "sin(-7+x)"))


;;;
;;; Examples
;;;

(define x 'x) (define y 'y) (define z 'z) (define h 'h)

(define (examples)
  (let ()
    (displayln "Is tan'(x) = 1 +tan(x)^2 ?")
    (equal? (diff (Tan x) x) (expand (⊕ 1 (Sqr (Tan x))))))
  (let ()
    (displayln "Proof of (x^2)' = 2x.")
    (define (f x) (⊗ x x))
    (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
    (define Δy/h (expand (⊘ Δy h)))
    (displayln (limit Δy/h h 0))) ; evaluates to (* 2 x)  
  (let ()
    (displayln "Proof of (x^3)' = 3x^2")
    (define (f x) (⊗ x x x))
    (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
    (define Δy/h (expand (⊘ Δy h)))
    (displayln (limit Δy/h h 0))) ; evaluates to (* 3 (expt x 2))  
  (let () 
    (displayln "Symmetric polynomials in 4 variables")
    (map displayln 
         (map expand 
              (coefficient-list (for/⊗ ([xi '(x1 x2 x3 x4)]) 
                                       (⊕ 1 (⊗ xi x))) x))))
  #;'(1
      (+ x1 x2 x3 x4)
      (+ (* x1 x2) (* x1 x3) (* x1 x4) (* x2 x3) (* x2 x4) (* x3 x4))
      (+ (* x1 x2 x3) (* x1 x2 x4) (* x1 x3 x4) (* x2 x3 x4))
      (* x1 x2 x3 x4))  
  (let () ; Pascal's triangle
    (displayln "Pascal's triangle")
    (for/list ([n 10]) 
      (displayln (coefficient-list (normalize `(expt (+ x 1) ,n)) x)))
    (void))
  (let ()
    (let ([u (expand '(* (- x 1) (expt (- x 2) 2) (- x 4)))])
      (define eqn (Equal u 0))
      (displayln (~a "Solving: " eqn))
      (displayln (solve eqn x)))
    ; Solving: (= (+ 16 (* -36 x) (* 28 (expt x 2)) (* -9 (expt x 3)) (expt x 4)) 0)
    ; '(or (= x 2) (= x 2) (= x 4) (= x 1))
    ))

(module+ start
  (provide quote quasiquote)
  (require (submod ".."))
  (require (prefix-in old: (only-in racket/base quote quasiquote)))
  ; In the REPL it can be convenient to change the meaning of ' 
  ; to automatic normalization:
  (define-syntax (quote stx) 
    (syntax-case stx () [(_ . datum) #'(normalize (old:quote . datum))]))
  (define-syntax (quasiquote stx) 
    (syntax-case stx () [(_ . datum) #'(normalize (old:quasiquote . datum))])))

; (let () (define f '(* x x)) `(* x ,f))  

; This macro doesn't work as expected ... why?
(define-syntax (repl stx) 
  (syntax-case stx () 
    [_ (with-syntax ([req (datum->syntax stx 'require)])
         (syntax/loc stx (req (submod "." start))))]))

;;; Example from the REPL.

; Require start makes ' automatically normalize all expressions.

(displayln "Enter the following in the REPL to redefine ' to do automatic simplification.")
(write '(require (submod "." start))) (newline)
;> (require (submod "." start))
;> '(+ x 1)
;'(+ 1 x)
;> '(+ x 1 y)
;'(+ 1 x y)
;> (limit '(sin x) x 0)
;0
;> (limit '(cos x) x 0)
;1
;> '(expt (+ x y) 3)
;'(expt (+ x y) 3)
;> (expand '(expt (+ x y) 2))
;'(+ (expt x 2) (expt y 2) (* 2 x y))
