#lang racket
(provide (all-defined-out))
(require (prefix-in % "bfracket.rkt"))
(require (only-in math/base cosh sinh))
(define debugging? #f)
(define verbose-debugging? #f)
(define (debug!) (set! debugging? (not debugging?)) debugging?)
(define (verbose-debug!) (set! verbose-debugging? (not verbose-debugging?)) verbose-debugging?)

; (debug!)

; Short term:
;   - fix: (App (Compose Expt Sin) 0)
;   - documentation
;   - simplify: rewrite fractions with square roots in the denominator
;   - in-terms  ( in-terms/proc is done )
;   - polynomial?
;   - use multivariable polynomial-quotient/remainder to simplify trig (cos^2+sin^2=1)
;   - power-expand
;   - Implement Integer pattern that accepts @n as an integer
;   - split expand into expand-one and expand (-all)
;   - examine automatic simplification of output of (diff '(expt x x) x)
;   - (Sqrt -3) currently returns (expt -3 1/2)
;     what is the correct error?
;   - (expt -8 1/3) does not return -2. Instead the principal value is returned.
;     NSpire for one returns -2. What is the best approach?
; Ideas:
;   - implement bfracket where big floats are numbers
;   - add arctan
;   - add factor
;   - use factor in solve
;   - unparse (for better presentation of results)
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
(module+ test
  (newline) (newline) (displayln "-------------------------------") (newline) (newline))

; Control Parameters
(define lazy-expt?    (make-parameter #f))
(define real-mode?    (make-parameter #t))
(define complex-mode? (make-parameter #f))
(define (complex-mode)
  (real-mode?    #f)
  (complex-mode? #t))
(define (real-mode)
  (real-mode?    #t)
  (complex-mode? #f))


(define-syntax (fluid-let stx)
  (syntax-parse stx
    [(_ ([var:id e:expr] ...) body ...)
     (with-syntax ([(t ...) (generate-temporaries #'(var ...))])
       (syntax/loc stx
         (let ([t var] ...)
           (set! var e) ...
           (begin0 (begin body ...)
                   (begin (set! var t) ...)))))]))

;;; A SYMBOLIC EXPRESSION is :
;;;   <sym> ::= <num> | <var> | (<var> <sym> ...)
;;; where
;;;   <num> is a Racket number
;;;   <var> is a Racket symbol
;;; Expressions of the form (<var> <sym> ...) will be called applications.

;;; SYMBOLIC CONSTANTS
(define @e  '@e)  ; Euler's constant
(define @pi '@pi) ; pi
(define @i  '@i)   ; the unit imaginary number
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
                                           (and (quote @p) (bind: u '@p)))])))
(module+ test 
  (check-equal? (match 41    [(Integer x) x]) 41)
  (check-equal? (match '@n   [(Integer x) x]) '@n)
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
  (displayln "TEST - Matcher: oplus")
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
  (displayln "TEST - Matcher: otimes")           
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
  (displayln "TEST - Matcher: ktimes")
  (check-equal? (match '(* 3 a b) [(k⊗ x y) (list x y)]) '(3 (* a b)))
  (check-equal? (match '3         [(k⊗ x y) (list x y)]) '(1 3))
  (check-equal? (match 'a         [(k⊗ x y) (list x y)]) '(1 a))
  (check-equal? (match '(* a b)   [(k⊗ x y) (list x y)]) '(1 (* a b)))
  (check-equal? (match '(* a b c) [(k⊗ x y) (list x y)]) '(1 (* a b c)))
  (check-equal? (match '(sin x)   [(k⊗ r u) (list r u)]) '(1 (sin x))))

;;; The pattern (Sum us) matches a sum of the form (+ u ...) and binds us to (list u ...)
(define-match-expander Sum
  (λ (stx) (syntax-case stx () [(_ us) #'(cons '+ us)])))
;;; The pattern (Prod us) matches a product of the form (* u ...) and binds us to (list u ...)
(define-match-expander Prod
  (λ (stx) (syntax-case stx () [(_ us) #'(cons '* us)])))

(module+ test
  (displayln "TEST - Matcher: Prod")
  (check-equal? (match '(*) [(Prod us) us]) '())
  (check-equal? (match '(* x) [(Prod us) us]) '(x))
  (check-equal? (match '(* x y) [(Prod us) us]) '(x y))
  (check-equal? (match '(* x y) [(Prod (list (== x) b)) b]) 'y)
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


;; The pattern (Complex u v) matches all expressions and
;; binds u to the "real" part and v to the "imaginary" part.

;;   (Complex u v) matches       @i                   and binds v->1,             u->0
;;   (Complex u v) matches    (* @i a)                and binds v->a,             u->0
;;   (Complex u v) matches    (* @i a b ...)          and binds v->(* a b ...)  , u->0
;;   (Complex u v) matches (+    @i          c)       and binds v->1,             u->c
;;   (Complex u v) matches (+    @i          c d ...) and binds v->1,             u->(+ c d ...)
;;   (Complex u v) matches (+ (* @i a)       c)       and binds v->a,             u->c
;;   (Complex u v) matches (+ (* @i a)       c d ...) and binds v->a,             u->(+ c d ...)
;;   (Complex u v) matches (+ (* @i a b ...) c d ...) and binds v->(* a b ...),   u->(+ c d ...)
;;   (Complex u v) matches _                          and binds v->0,             u->a)

;; In short:
;;    After a match  (⊕ (⊗ @i u) v) is equal to the matched expression.

(module+ test
  (displayln "TEST - Matcher: Complex")
  (check-equal? (match     @i              [(Complex u v) (list u v)] [_ #f]) '(0 1))
  (check-equal? (match '(* @i 3)           [(Complex u v) (list u v)] [_ #f]) '(0 3))
  (check-equal? (match '(* @i 3 x)         [(Complex u v) (list u v)] [_ #f]) '(0 (* 3 x)))
  (check-equal? (match '(+ @i   x)         [(Complex u v) (list u v)] [_ #f]) '(x 1))
  (check-equal? (match '(+ @i   x y)       [(Complex u v) (list u v)] [_ #f]) '((+ x y) 1))
  (check-equal? (match '(+ (* @i 3) x)     [(Complex u v) (list u v)] [_ #f]) '(x 3))
  (check-equal? (match '(+ (* @i 3) x y)   [(Complex u v) (list u v)] [_ #f]) '((+ x y) 3))
  (check-equal? (match '(+ (* @i 3 z) x y) [(Complex u v) (list u v)] [_ #f]) '((+ x y) (* 3 z)))
  (check-equal? (match '(+ x y)            [(Complex u v) (list u v)] [_ #f]) '((+ x y) 0)))


(define (Complex: u v)
  (⊕ (⊗ @i v) u))

(define-match-expander Complex
  ; Note: This matches everything and writes it as a complex, even when real or imag equals to 0.
  (λ (stx)
    (syntax-parse stx
      [(_ v u)
       (syntax/loc stx
         (or (and           '@i                                 (bind: u 1)  (bind: v 0))
             (and (list  '* '@i u)                                           (bind: v 0))
             (and (list* '* '@i (app (λ(ys) (cons '* ys)) u))                (bind: v 0))
             (and (list  '+ '@i v)                              (bind: u 1))
             (and (list* '+ '@i (app (λ(ys) (cons '+ ys)) v))   (bind: u 1))
             (and (list  '+ (list  '* '@i u)                                                        v))
             (and (list* '+ (list  '* '@i u)                              (app (λ(ys) (cons '+ ys)) v)))
             (and (list  '+ (list* '* '@i (app (λ(ys) (cons '* ys)) u))                             v))
             (and (list* '+ (list* '* '@i (app (λ(ys) (cons '* ys)) u))   (app (λ(ys) (cons '+ ys)) v)))
             (and v (bind: u 0))))]))
  (λ (stx)
    (syntax-parse stx [(_ u v) #'(Complex: u v)] [_ (identifier? stx) #'Complex:])))


;; The pattern (ImaginaryTerm u) matches imaginary terms and binds
;; u to the coefficient.

;;   (ImaginaryTerm u v) matches       @i                   and binds v->1
;;   (ImaginaryTerm u v) matches    (* @i a)                and binds v->a
;;   (ImaginaryTerm u v) matches    (* @i a b ...)          and binds v->(* a b ...)

(module+ test
  (displayln "TEST - Matcher: ImaginaryTerm")
  (check-equal? (match     @i              [(ImaginaryTerm u) u] [_ #f]) 1)
  (check-equal? (match '(* @i 3)           [(ImaginaryTerm u) u] [_ #f]) 3)
  (check-equal? (match '(* @i 3 x)         [(ImaginaryTerm u) u] [_ #f]) '(* 3 x))
  (check-equal? (match '(+ x y)            [(ImaginaryTerm u) u] [_ #f]) #f))


(define (ImaginaryTerm: u)
  (⊗ @i u)) 

(define-match-expander ImaginaryTerm
  ; Note: This matches everything only if the imaginary part is non-zero.  
  (λ (stx)
    (syntax-parse stx
      [(_ u)
       (syntax/loc stx
         (or (and           '@i      (bind: u 1))
             (and (list  '* '@i u))
             (and (list* '* '@i (app (λ(ys) (cons '* ys)) u)))))]))
  (λ (stx)
    (syntax-parse stx [(_ u) #'(ImaginaryTerm: u)] [_ (identifier? stx) #'ImaginaryTerm:])))


;;; The pattern (Piecewise us vs) matches a piecewise expression of
;;; the form (piecewise [u v] ...) 
;;; and binds us to (list u ...) 
;;; and binds vs to (list v ...) 
(define-match-expander Piecewise
  (λ (stx)
    (syntax-case stx ()
      [(_ u c)
       #'(list 'piecewise (list u c) (... ...))]))
  (λ (stx)
    (syntax-case stx ()
      [(_ (u v) ...) #'(list 'piecewise (list u v) ...)]
      [_ (identifier? stx) #'piecewise])))

(define-syntax (piecewise stx)
  (syntax-parse stx
    [(_ [u:expr v:expr] ...)
     (syntax/loc stx (cond [v u] ...))]))


#|
;;; ASSUMPTIONS
; This idea has been postponed.
(define assumptions (make-hash))
(define (get-assumptions var)     (hash-ref assumptions var '()))
(define (add-assumption! var tag) (hash-set! assumptions var (cons tag (get-assumptions tag))))
(define (assume-real var)         (add-assumption! var 'real))
(define (assume-positive var)     (add-assumption! var 'positive))
(define (assume-negative var)     (add-assumption! var 'negative))

(define (Positive? u)
  (and (math-match u
         [r.      (positive? r.)]
         ; [r.bf    (bfpositive? r.bf)]
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

(define (symbol<<? x y)
  ; The symbol @i gets special treatment.
  ; Note: Not needed for <<, but symbol<<? might be useful elsewhere.
  (cond
    [(eq? x y)   #f]
    [(eq? x '@i) #t]
    [(eq? y '@i) #f]
    [else        (symbol<? x y)]))

(define (<< s1 s2)
  ; (displayln (list '<<= s1 s2)) ; uncomment in case of infinite loop
  (math-match* (s1 s2)
    [((ImaginaryTerm u) s2) 
     (math-match s2
                 [(ImaginaryTerm v) (<< u v)]
                 [v                 #t])]
    [(u (ImaginaryTerm v))                 #f]    
    ; Case: at least one number
    [(r s) #:when (and (real? r) (real? s)) (< r s)] ; fast path for two reals
    [(r _) #t]
    [(u r) #f]
    ; Case: at least one big float
    [(r.bf s.bf) (bf< r.bf s.bf)]
    [(r.bf _) #t]
    [(u r.bf) #f]
    ; Case: at least one boolean
    [(bool1 bool2) (and bool1 (not bool2))] ; #t < #f
    [(bool u)      #t]
    [(u bool)      #f]
    ; Case: At least one symbol
    [(x y) (symbol<<? x y)]
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
       [(x y) (symbol<<? x y)]
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
        (or (symbol<<? f g)
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
  (displayln "TEST - <<")
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
  (check-equal? (<< '(* 2 (+ -1.0 x)) '(* 3 (expt (+ -1.0 x) 2))) #t)
  ; @i is always the first symbol
  (check-equal? (<< '@i '@a) #t) 
  (check-equal? (<< '@a '@i) #f)
  (check-equal? (<< '@i '@z) #t)
  (check-equal? (<< '@z '@i) #f)
  (check-equal? (<< '@i 'a)  #t) 
  (check-equal? (<< 'a '@i)  #f)
  (check-equal? (<< '@i '@i) #f)
  ; @i precedes all other types of expressions
  (check-equal? (<< '@i 1)           #t)
  (check-equal? (<< '@i 1.2)         #t)
  (check-equal? (<< '@i '(+ 1 x))    #t)
  (check-equal? (<< '@i '(* 1 x))    #t)
  (check-equal? (<< '@i '(f x))      #t)
  (check-equal? (<< '@i '(sin x))    #t)
  (check-equal? (<< '@i '(expt x 2)) #t))

;; (⊕ u ...) in an expression context expands to (plus u ...)
;; That is: Elsewhere use ⊕ in order to add expressions.
;; Note: plus assumes the expressions are canonical.
(define (plus . us) (foldl plus2 0 us))
(define (plus2 s1 s2)
  ; '(+ (* 2 c) (* a b) (* 3 c))
  (when verbose-debugging? (displayln (list 'plus2 s1 s2)))
  ; Note: all recursive calls must reduce size of s1
  ; Note: This is the first use of math-match in this file.
  ; The conventions in math-match are:
  ;   r and s matches only numbers
  ;   x and y matches only symbols
  ;   @e and @pi matches only '@e and '@pi  
  (math-match* (s1 s2)
    ; handle reals
    [(0 u) u]
    [(u 0) u]
    [(r s)    (+ r s)]
    ; [(r.bf s.bf) (bf+ r.bf s.bf)]    ; xxx
    ; [(r s.bf)    (bf+ (bf r) s.bf)]  ; xxx
    ; [(r.bf s)    (bf+ r.bf (bf s))]  ; xxx
    ; handle at least one complex 
    [((Complex u1 v1) (Complex u2 v2)) #:when (not (and (equal? v1 0) (equal? v2 0)))
                                       (define u1+u2 (plus2 u1 u2)) ; real part
                                       (define v1+v2 (plus2 v1 v2)) ; imag part
                                       (match* (u1+u2 v1+v2 )
                                         [(0 0) 0]
                                         [(v 0) v]
                                         [(0 1) @i]
                                         [(0 u) (⊗ @i u)]
                                         [(v 1) `(+ @i ,v)]
                                         [(v u) `(+ ,(⊗ @i u) ,v)])]
    ; other
    [(u s) (plus2 s u)]  ; ok since u can not be a number nor @i, we have that s <<= u
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
  (displayln "TEST - Plus")
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
                '(+ (f x) (f (+ h x)) (f (+ (* 2 h) x))))
  ;;; complex
  (check-equal? (⊕ @i)                            @i)
  (check-equal? (⊕ @i @i)                     `(* @i 2))
  (check-equal? (⊕ @i @i @i)                  `(* @i 3))
  (check-equal? (⊕ @i 0)                          @i)
  (check-equal? (⊕ 0 @i)                          @i)  
  (check-equal? (⊕ @i 1)                `(+       @i 1))  
  (check-equal? (⊕ @i 1.0)              `(+       @i 1.))
  
  (check-equal? (⊕ @i `(* @i 3))              `(* @i 4))
  (check-equal? (⊕ `(* @i  3) `(* @i 4))      `(* @i 7))
  (check-equal? (⊕ `(* @i  3)     @i)         `(* @i 4))
  (check-equal? (⊕ `(* @i  3)     @i 2)   `(+  (* @i 4) 2))
  (check-equal? (⊕ `(* @i -1)     @i)                   0)
  (check-equal? (⊕     @i     `(* @i -1))               0)
  (check-equal? (⊕ (⊕ `(* @i 3 a) 1) @i)  `(+ (* @i (+ 1 (* 3 a))) 1)) 
  (check-equal? (⊕ (⊕        @i 1)    (⊕     @i      2)) `(+ (* @i 2) 3))
  (check-equal? (⊕ (⊕ `(* @i 3) 1)    (⊕     @i      2)) `(+ (* @i 4) 3))
  (check-equal? (⊕ (⊕ `(* @i 3) 1)    (⊕ `(* @i 5)   2)) `(+ (* @i 8) 3))
  (check-equal? (⊕ (⊕     @i 2)       (⊕ `(* @i 3)   1)) `(+ (* @i 4) 3))
  (check-equal? (⊕ (⊕ `(* @i 3 a) 1)  (⊕ `(* @i 4 a) 3)) `(+ (* @i 7 a) 4))
  (check-equal? (⊕ (⊕ `(* @i 3 a) 1)  (⊕ `(* @i 4 b) 3))
                '(+ (* @i (+ (* 3 a) (* 4 b))) 4)))

;; (⊗ u ...) in an expression context expands to (times u ...)
;; That is: Elsewhere use ⊗ in order to multiply expressions.
;; Note: times assumes the expressions are canonical.
(define (times . xs) (foldl times2 1 xs))
(define (times2 s1 s2)
  (when verbose-debugging? (displayln (list 'times2 s1 s2)))
  (math-match* (s1 s2)
    [(0 u) 0] [(u 0) 0]
    [(1 u) u] [(u 1) u]
    [(r s)    (* r s)]
    
    [(@i @i)  -1]
    [(@i 1)   @i]
    [(@i r)   `(* @i ,r)]
    [(u  @i)  (times2 @i u)]
    
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
    [(x y) (if (symbol<<? x y) (list '* x y) (list '* y x))]
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
  (displayln "TEST - times")
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

; Note: In normalized expressions all numbers are real.
;       A complex number, say, 2+3i, is rewritten to (+ 2 (* 3 @i))

(define (normalize u)
  (when debugging? (displayln (list 'normalize u)))
  (define (normalize-complex-number r)
    (define a (real-part r))
    (define b (imag-part r))
    (if (zero? a) (⊗ @i b) (⊕ (⊗ @i b) a)))
  (define n normalize)
  (math-match u
    [r #:when (real? r) r]    ; fast path
    [r (normalize-complex-number r)]
    [r.bf r.bf]
    [#t #t]
    [#f #f]
    [x x]
    [(⊕ u)              (n u)]
    [(⊕ u v)            (⊕ (n u) (n v))]
    [(⊗ u)              (n u)]
    [(⊗ u v)            (⊗ (n u) (n v))]
    [(And u v)          (And (n u) (n v))]
    [(Or u v)           (Or (n u) (n v))]
    [(And u)            (And (n u))]
    [(Or u)             (Or  (n u))]
    [(Expt u v)         (Expt (n u) (n v))]
    [(Equal u v)        (Equal        (n u) (n v))] ; xxx
    [(Less u v)         (Less         (n u) (n v))]
    [(LessEqual u v)    (LessEqual    (n u) (n v))]
    [(Greater u v)      (Greater      (n u) (n v))]
    [(GreaterEqual u v) (GreaterEqual (n u) (n v))]    
    [(Ln u)             (Ln   (n u))]
    [(Log u)            (Log  (n u))]
    [(Log u v)          (Log  (n u) (n v))]
    [(Sin u)            (Sin  (n u))]
    [(Asin u)           (Asin (n u))]
    [(Atan u)           (Atan (n u))]
    [(Cos u)            (Cos  (n u))]
    [(Acos u)           (Acos (n u))] 
    [(Cosh u)           (Cosh (n u))]
    [(Sinh u)           (Sinh (n u))]
    [(Abs u)            (Abs  (n u))]
    [(Magnitude u)      (Magnitude (n u))]
    [(Angle u)          (Angle (n u))]
    [(Factorial u)      (Factorial (n u))]
    [(Gamma u)          (Gamma (n u))]
    [(Prime? u)         (Prime? (n u))]
    [(Odd-prime? u)     (Odd-prime? (n u))]
    [(Nth-prime u)      (Nth-prime (n u))]
    [(Random-prime u)   (Random-prime (n u))]
    [(Next-prime u)     (Next-prime (n u))]
    [(Prev-prime u)     (Prev-prime (n u))]
    [(Divisors u)       (Divisors (n u))]    
    [(Piecewise us vs)  (list* 'piecewise (map list (map n us) (map n vs)))]
    [(app: f us) (match u
                   [(list  '/ u v)    (⊘ (n u) (n v))]
                   [(list  '- u)      (⊖ (n u))]
                   [(list  '- u v)    (⊖ (n u) (n v))]
                   [(list  'tan v)    (Tan  (n v))]
                   [(list  'sqr u)    (Sqr  (n u))]
                   [(list  'sqrt u)   (Sqrt (n u))]
                   [(list  'root u m) (Root (n u) (n m))]
                   [(list  'exp u)    (Exp  (n u))]  
                   [(list  'bf u)     (number? u) (bf u)]
                   [(list* 'or us)    (apply Or: us)]
                   [_ (let ([nus (map n us)])
                        (if (equal? us nus)
                            u
                            (n `(,f ,@nus))))])]))

(module+ test
  (displayln "TEST - normalize")
  (check-equal? (normalize '(+ 1 x (* (expt (sin (ln (cos (asin (acos (sqrt (tan x))))))) 2))))
                (⊕ 1 x (⊗ (Expt (Sin (Ln (Cos (Asin (Acos (Sqrt (Tan x))))))) 2))))
  (check-equal? (normalize '(/ (- x) (+ (- x y) (exp x) (sqr x) (+ 3)))) 
                (⊘ (⊖ x) (⊕ (⊖ x y) (Exp x) (Sqr x) (⊕ 3))))
  (check-equal? (normalize '(bf 3)) (bf 3))
  (check-equal? (normalize '(f (- x y))) `(f ,(⊖ x y)))
  (check-equal? (normalize '(log 3)) '(log 10 3))
  ; check that complex numbers are normalized to the form (+ a (* b @i))
  (check-equal? (normalize  +i)     '@i)
  (check-equal? (normalize 1+i)  '(+ @i 1))
  (check-equal? (normalize  +2i) '(* @i 2))
  ; check that @i appears as the first symbol in products
  (check-equal? (normalize '(* 2 x a z 3 y @a @z @i )) '(* @i 6 @a @z a x y z)))


; Compile turns an expression into a Racket function.
(define (compile u [x 'x])
  ; todo: check that x is the only free variable in u
  (eval `(λ (,x) ,u) (make-base-namespace)))

(module+ test (check-equal? ((compile '(sin (sqrt x))) 0) 0))

; distribute applies the distributive law recursively
(define (distribute s)
  (when debugging? (displayln (list 'distribute s)))
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
  (displayln "TEST - distribute")
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
    [(Expt (⊕ u v) p-) (Expt (e (Expt (⊕ u v) (- p-))) -1)]
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
  (check-equal? (expand (Expt (⊕ x y) -2)) (Expt (⊕ (Sqr x) (Sqr y) (⊗ 2 x y)) -1))
  (check-equal? (expand (Expt (⊕ x y) 4)) (expand (⊗ (Sqr (⊕ x y)) (Sqr (⊕ x y)))))
  (check-equal? (expand (⊗ (⊕ x y) (Cos x))) '(+ (* x (cos x)) (* y (cos x))))
  (check-equal? (expand (Ln (Expt x 3))) (⊗ 3 (Ln x)))
  (check-equal? (expand '(* 2 x (+ 1 x))) (⊕ (⊗ 2 x) (⊗ 2 (Sqr x))))
  (check-equal? (expand '(* (expt (+ 1 x) 2) (sin 2))) 
                '(+ (* 2 x (sin 2)) (* (expt x 2) (sin 2)) (sin 2)))

  (check-equal? (normalize '(+ 2 (* -3 (expt 2 -1) x) (* 3 x))) '(+ 2 (* 3/2 x)))
  (check-equal? (expand-all '(* @i (+ 4 (* -1 (+ (* 4 x) 2))))) '(* @i (+ 2 (* -4 x)))))


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


;;;
;;; Quotients
;;;

; For a rational number a/b the numerator and denominator are a and b respectively. 
; For an expression u which happen be a ratio (a product of a rational and factors
; of the form (expt u p) we compute the numerator and denominator.
; For other expressions 1 is returned as a denominator.

; When matching we will in some situations want to match a "real" quotient,
; i.e. one where the denominator isn't 1. So we will define two different match
; expanders ⊘ and Quotient. Here ⊘  matches only if the denominator isn't 1,
; and Quotient will match all expressions.

; To sum up:
;   (match u [(⊘ u1 v1) ...])  should bind u1 to (numerator u) and v1 to (denominator u) 
;                                     but only if the denominator isn't 1.

; Maxima:
;   Returns the numerator of expr if it is a ratio. If expr is not a ratio, expr is returned.

; In comparison Mathematica will use `together` before returning the numerator/denominator.

; The pattern Quotient will use numerator/denominator.
; The pattern QuotientTogether will call `together` first.

; divide u by v
(define (Oslash: u v)
  (match* (u v)
    [((num: r)  0) +nan.0]
    [(u  1) u]
    [(u -1) (⊖ u)]
    [(u u) 1]  ; should trigger a warning: x/x=1 is not true when x=0
    [((TimesTerms (== v) us ...) _) (apply ⊗ us)]
    [(u  v) (⊗ u (Expt v -1))]))

(define (not-one? x) (not (equal? x 1)))

(define-match-expander ⊘
  ; Note: This matches one kind of quotient, i.e., a product with a non-one denominator.
  ; Use term-numerator/denominator so that (⊘ u v) can match '(* 3 (expt x -1) y)
  (λ (stx) (syntax-parse stx [(_ u v) #'(app numerator/denominator u (? not-one? v))]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Oslash: u v)] [_ (identifier? stx) #'Oslash:])))

(module+ test
  (displayln "TEST - OSLASH")
  (check-equal? (Oslash: '(* (cos x) (+ 1 x)) '(+ 1 x))  '(cos x))
  (check-equal? (math-match 2/3                       [(⊘ u v) (list u v)] [_ #f]) '(2 3))  
  (check-equal? (math-match (⊘ x y)                   [(⊘ u v) (list u v)] [_ #f]) '(x y))
  (check-equal? (math-match (⊗ x (Expt (⊗ 2 y z) -1)) [(⊘ u v) (list u v)] [_ #f]) '(x (* 2 y z)))
  (check-equal? (math-match (⊘ (⊗ y 3) x)             [(⊘ u v) (list u v)] [_ #f]) '((* 3 y) x))
  (check-equal? (math-match '(* 2/3 x)                [(⊘ u v) (list u v)] [_ #f]) '((* 2 x) 3)))

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

(define (Quotient: u v)
  (⊘ u v))

(define-match-expander Quotient
  ; Note: This matches everything and writes it as a quotient.
  (λ (stx) (syntax-parse stx [(_ u v) #'(and (app numerator u) (app denominator v))]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Quotient: u v)] [_ (identifier? stx) #'Quotient:])))

(module+ test
  (displayln "TEST - QUOTIENT")
  (check-equal? (math-match 2/3             [(Quotient u v) (list u v)] [_ #f]) '(2 3))
  (check-equal? (math-match '(* 2.3 x)      [(Quotient u v) (list u v)] [_ #f]) '((* 2.3 x) 1))
  (check-equal? (math-match (⊘ x (⊗ 2 y z)) [(Quotient u v) (list u v)] [_ #f]) '(x (* 2 y z)))
  (check-equal? (math-match (⊘ x y)         [(Quotient u v) (list u v)] [_ #f]) '(x y))
  (check-equal? (math-match (⊘ (⊗ y 3) x)   [(Quotient u v) (list u v)] [_ #f]) '((* 3 y) x))
  ; (check-equal? (math-match (⊕ x 2/3)       [(Quotient u v) (list u v)] [_ #f]) '((+ 2 (* 3 x)) 3)) ; not simple
  )

(define (numerator u)
  (math-match u
    [r                                      (%numerator u)]
    [r.bf                                   (%numerator u)]
    [(Expt u r-)                            1]
    [(Expt u (⊗ r- us))                     1]    
    [(⊗ u v)                                (⊗ (numerator u) (numerator v))]
    [_                                      u]))

(define (denominator u)
  (math-match u
    [r                                      (%denominator u)]
    [r.bf                                   (%denominator u)]
    [(Expt u r-)                            (Expt u (- r-))]
    [(Expt u (⊗ r- us))                     (Expt u (⊗ (- r-) us))]
    [(⊗ u v)                                (⊗ (denominator u) (denominator v))]
    [_                                      1]))

(define (numerator/denominator u)
  (values (numerator u) (denominator u)))

(module+ test
  (displayln "TEST - DENOMINATOR")
  (check-equal? (denominator 2)               1)
  (check-equal? (denominator 0.5)             1)
  (check-equal? (denominator 2/3)             3)
  (check-equal? (denominator y)               1)
  (check-equal? (denominator (bf 1.2))        1)
  (check-equal? (denominator (Sqrt x))        1)
  (check-equal? (denominator (⊘ 2 x))         x)
  (check-equal? (denominator (⊗ 3/5 (⊘ 2 x))) (⊗ 5 x))
  (check-equal? (denominator (Expt 'y (⊖ 'm))) (Expt 'y 'm)))

(module+ test
  (displayln "TEST - NUMERATOR")
  (check-equal? (numerator 2) 2)
  (check-equal? (numerator 2.1) 2.1)
  (check-equal? (numerator 2/3) 2)
  (check-equal? (numerator pi.bf) pi.bf)
  (check-equal? (numerator 'a) 'a)
  (check-equal? (numerator '(⊕ (⊘ 1 x) (⊘ 1 y))) '(⊕ (⊘ 1 x) (⊘ 1 y)))
  (check-equal? (numerator (⊘ 2 x)) 2)
  (check-equal? (numerator (⊗ 3/5 (⊘ 2 x))) (⊗ 3 2))
  (check-equal? (numerator (⊘ x y)) x)
  (check-equal? (numerator (Expt 'y (⊖ 'm))) 1))


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


(require (submod "math-match.rkt" predicates))


;;;
;;; TERM MANIPULATION
;;;

;;; Negative Term

; A term of the form
;   r or (* r u)
; where r is a negative number is wille be called a *negative-term*.

(define (negative-term? u)
  ; we assume u is normalized, so we don't need to look at other
  ; factors besides the first one.
  (math-match u
    [r       #:when (negative? r) #t]
    [(⊗ r v) #:when (negative? r) #t]
    [_                            #f]))

(module+ test
  (displayln "TEST - negative-term?")
  (check-equal? (negative-term? (normalize '(* -2 x (log 3)))) #t)
  (check-equal? (negative-term? (normalize '(* x (* -2 y) z))) #t)
  (check-equal? (negative-term? (normalize 1+i))               #f)
  (check-equal? (negative-term? (normalize '(+ x -10)))        #f))


;;; Partition a sum into positive and negative terms.

(define (partition-terms-after-sign u)
  ; Given a sum u, two normalized expressions u_pos and u_neg such
  ; that u = u_pos - u_neg are returned.
  ; The sum u_neg consists of all negative terms in u (with signs negated).

  ; Implementation note: If u is normalized, then so will a partial sum,
  ; if we keep the original order.  
  (define (reverse-terms->sum vs)    
    (match vs
      ['()      0]
      [(list v) v]
      [_        (cons '+ (reverse vs))])) ; a partial sum is normalized
  (define (negate-term v)
    (math-match v
      [r          (- r)]
      [(⊗ r u) (⊗ (- r) u)]
      [_ (error)]))
  (match u
    [r #:when (and (real? r) (negative? r)) (values 0 (- r))]
    [r #:when      (real? r)                (values r 0)]
    [x #:when (symbol? x)                   (values x 0)] ; assume variables are positive
    [(list* '+ us) (let loop ([us us] [pos '()] [neg '()])
                     (match us
                       ['()         (values (reverse-terms->sum pos)
                                            (reverse-terms->sum neg))]
                       [(cons u us) (if (negative-term? u)
                                        (loop us         pos  (cons (negate-term u) neg))
                                        (loop us (cons u pos)                       neg))]))]
    [_ (values u 0)]))
                        

  
(module+ test
  (displayln "TEST - partition-terms-after-sign")
  (let-values ([(p n) (partition-terms-after-sign (normalize '(+ (exp 5) (* -2 x) z 2/3)))])
    (check-equal? p (normalize '(+ 2/3 z (exp 5))))
    (check-equal? n '(* 2 x)))
  (let-values ([(p n) (partition-terms-after-sign -7)])
    (check-equal? p 0)
    (check-equal? n 7))
  (let-values ([(p n) (partition-terms-after-sign  7)])
    (check-equal? p 7)
    (check-equal? n 0))
  (let-values ([(p n) (partition-terms-after-sign '@i)])
    (check-equal? p '@i)
    (check-equal? n 0)))


(define (term-numerator/denominator s)
  (numerator/denominator s))


(module+ test
  (displayln "TEST - term-numerator/denominator")
  (let-values ([(n d) (term-numerator/denominator (normalize '(* (/ x y) z 2/3)))])
    (check-equal? n '(* 2 x z))
    (check-equal? d '(* 3 y))))

; used for quotient.
; first call together, then split up the term-numerator/denominator parts.
; differences can be indicated by the following tests.
(define (mma-numerator/denominator s)
  (term-numerator/denominator (together s)))


(module+ test
  (displayln "TEST - term-numerator/denominator")
  (let-values ([(n d) (term-numerator/denominator (normalize '(+ (/ x y) 2/3)))])
    (check-equal? n '(+ 2/3 (* x (expt y -1))))
    (check-equal? d 1))
  (let-values ([(n d) (mma-numerator/denominator (normalize '(+ (/ x y) 2/3)))])
    (check-equal? n '(+ (* 3 x) (* 2 y)))
    (check-equal? d '(* 3 y)))
  ; test cases adapted from https://reference.wolfram.com/language/ref/NumeratorDenominator.html?view=all
  (let-values ([(n d) (numerator/denominator 2/3)])
    (check-equal? n 2)
    (check-equal? d 3))
  (let-values ([(n d) (numerator/denominator (normalize '(* (+ x -1) (+ x -2) (expt (+ x -3) -2))))])
    (check-equal? n '(* (+ -2 x) (+ -1 x)))
    (check-equal? d '(expt (+ -3 x) 2)))
  (let-values ([(n d) (mma-numerator/denominator (⊕ 3/7 (⊗ 1/11 @i)))])
    (check-equal? n '(+ (* @i 7) 33))
    (check-equal? d 77))
  ; Is this test case correct?
  #;(let-values ([(n d) (mma-numerator/denominator 
                         (⊗ 'a (Expt 'x 'n) (Expt 'y (⊖ 'm)) (Exp (⊕ 'a (⊖ 'b) (⊗ -2 'c) (⊗ 3 'd)))))])
      (check-equal? n '(* (expt @e (+ a (* 3 d))) a (expt x n)))
      (check-equal? d '(* (expt @e (* -1 (+ (* -1 b) (* -2 c)))) (expt y m))) ; better to simplify (* -1 (+ (* -1 b) (* -2 c))))
      ))

;;; Together

; The `together` operations rewrites a sum into a single fraction.
; A common denominator the terms in the sum is found.


(define (together u)
  (when debugging? (displayln (list 'together u)))
  (parameterize ([lazy-expt? #t])
    (together-impl u)))

(define (together-impl expr)
  (define t together-impl)
  (match expr
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
  (check-equal? (together (normalize '(+ (/ y 5) 1))) '(* 1/5 (+ 5 y))))

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


; minus :
;   constructs a normalized expression representing -u or u-v
;   where u and v are normalized expressions.
(define (minus . us)
  (match us
    ; unary and binary minus
    [(list u)   (⊗ -1 u)]
    [(list u v) (⊕ u (⊗ -1 v))]
    ; TODO: handle more minuends
    [_ (error)]))

(module+ test
  (displayln "TEST - minus")
  (check-equal? (minus 1)                    -1)
  (check-equal? (minus (minus 1))             1)
  (check-equal? (minus 'x)                   (⊗ -1 x))
  (check-equal? (minus (minus 'x))           'x)
  (check-equal? (minus 'x 1)                 (⊕ -1 'x))) 

(define (not-zero? x) (not (equal? x 0)))

(define-match-expander ⊖
  (λ (stx)
    (syntax-parse stx
      ; This matches terms with negative coeff.
      [(_ u) #'(app minus (? (negate negative-term?) u))]
      ; Note: This matches everything and writes it as a form of (subtrahend - minuend),
      ;       unless the minuend equals to 0.
      [(_ u v) #'(app partition-terms-after-sign u (? not-zero? v))]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(minus u ...)] [_ (identifier? stx) #'minus])))

(module+ test
  (displayln "TEST - minus match pattern")
  ; ⊖ u
  (check-equal? (match -41.3                 [(⊖ x) x])      41.3)
  (check-equal? (match '(* -1 y)             [(⊖ x) x])      'y)
  (check-equal? (match '(* -2 y)             [(⊖ x) x])      '(* 2 y))
  ; ⊖ u v
  (check-equal? (math-match -3               [(⊖ u v) (list u v)] [_ #f]) '(0 3))
  (check-equal? (math-match '(+ @i (* -3 x)) [(⊖ u v) (list u v)] [_ #f]) '(@i (* 3 x))))

;; The pattern Exp matches the natural exponential function
;;  (Exp u) matches (expt @e a) and binds u->a
;; The symbol @e is symbolic representation of Euler's constant.
;; In an expression context (Exp u) is `(expt @e ,u))
(define (Exp: u) (Expt @e u))

(define-match-expander Exp
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt '@e u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Expt: '@e u)] [_ (identifier? stx) #'Exp:])))

(module+ test
  (check-equal? (match (Exp 2)       [(Exp u) u])        2)  
  (check-equal? (match (Expt '@e 2)  [(Exp u) u])        2)
  (check-equal? (match (Expt '@pi 2) [(Exp u) u] [_ #f]) #f)) ; make sure only @e is matched

(define (Expt: u v)
  (when debugging? (displayln (list 'Expt: u v 'lazy-expt? (lazy-expt?))))
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
  ; (displayln (list 'Expt u v))
  (math-match* (u v)
    [(1 v)          1]
    [(u 1)          u]
    [(0 0)          +nan.0] ; TODO: is this the best we can do?   
    [(0 v)          0]
    [(u 0)          1]
    [(u 0.0)        1.0]
    [(r.0 s)        (expt r.0 s)] ; inexactness is contagious
    [(r s.0)        (expt r s.0)] ; inexactness is contagious
    
    [(n  1/2)        (sqrt-natural n)]
    [(n -1/2)        (match (sqrt-natural n)
                       [α  #:when (real? α)                             (/ 1 α)]
                       [(list 'expt v 1/2)                              `(expt ,v -1/2)]
                       [(list '* α (list 'expt v 1/2)) (list '* (/ 1 α) `(expt ,v -1/2))]
                       [_ (error 'internal-error-in-expt:)])]
    ; [PR10, soegaard] uncommented. If u is a power, then `(expt ,u -1)` is not a
    ;                               normalized representation of u^-1.
    ; [(u -1) #:when (lazy-expt?) `(expt ,u ,-1)]

    [(p n)          (expt  p  n)] ; n>0 integer
    [(p q)          (expt  p  q)] ; q<0 (potentially handle 4^-1/2 and 8^-1/3)
    
    [(α p)          (expt  α  p)]
    [(p β)    #:when (real-mode?)
              (cond [(and (positive? β) (= (%numerator β) 1))
                     (define-values (root rem) (integer-root/remainder (abs p) (/ 1 β)))
                     (if (> p 0)
                         (if (= rem 0) root `(expt ,p ,β))
                         (if (and (= rem 0) (odd? (/ 1 β))) (- root) `(expt ,p ,β)))]
                    [else `(expt ,p ,β)])]
    [(p β)   #:when (complex-mode?) ; here we need the principal value
             (cond [(and (positive? β) (= (%numerator β) 1))
                    (define n (/ 1 β))
                    (define-values (root rem) (integer-root/remainder (abs p) (/ 1 β)))
                    (cond [(= rem 0) (if (negative? p) (⊗ root (ExpI (⊗ β @pi))) root)]
                          [else `(expt ,p ,β)])]
                   [else `(expt ,p ,β)])]
    [(α β)          (let ([n (%numerator α)] [d (%denominator α)])
                      (⊗ (Expt n β) (Expt d (⊖ β))))]              ; (n/d)^β = n^β * d^-β

    [(u  (Log u v)) v]                   ; xxx - is this only true for u real?
    [(@e (Ln v))    v]
    [(@e (⊗ p (Ln v)))  (Expt v p)]
    [(@e @i)        (ExpI 1)]
    [(@e x)        `(expt @e ,x)]    
    [(@e v)         (match v
                      [(list  '*   '@i '@pi)                  (ExpI @pi)]
                      [(list  '* r '@i '@pi) #:when (real? r) (ExpI (⊗ r @pi))] 
                      [_ `(expt @e ,v)])]
    
    [(@i α)             (ExpI (⊗ 1/2 α @pi))]
    [(@i (Complex a b)) (ComplexComplexExpt 0 1 a b)]
    ; we need to handle all @i cases before x is met (otherwise thus catches @i^_ 
    [(x  v)  #:when (not (eq? x '@e))    `(expt ,x ,v)]
    [((Expt u α) β) #:when (and (integer? (* α β)) (not (and (integer? α) (even? α))))
                    (Expt u (* α β))]
    [((Expt u v) p) (Expt u (⊗ p v))]
    [((Expt u -1) v) (Expt u (⊗ -1 v))]
    [((⊗ u v) p)    #:when (not (lazy-expt?))
                    (⊗ (Expt u p) (Expt v p))]
    [(u v)
     (cond
       [(real-mode?)  ; real mode
        (math-match* (u v)
          [((Expt u v) w)  (Expt u (⊗ v w))]           ; ditto    
          [((⊗ u v) w)    #:when (not (lazy-expt?))
                          (⊗ (Expt u w) (Expt v w))] ; xxx - only true for real u and v
          [(_ _)          `(expt ,u ,v)])]
       [(complex-mode?) ; complex mode
        (math-match* (u v)
          [((Complex a b) (Complex c d))
           (cond
             [(and (equal? b 0) (equal? d 0)) `(expt ,u ,v)] ; u might be a product
             ; avoid computing the partition into real and imaginary multiple times,
             ; so pass the a, b c and along.
             [(equal? d 0)               (ComplexRealExpt a b c)]
             [(equal? b 0)               (RealComplexExpt a c d)]
             [else                  (ComplexComplexExpt a b c d)])]
          [(_ _)          `(expt ,u ,v)])])]))

(define-match-expander Expt
  (λ (stx) (syntax-parse stx [(_ u v) #'(list 'expt u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Expt: u v)] [_ (identifier? stx) #'Expt:])))

(module+ test
  ; (debug!)
  (displayln "TEST - EXPT")
  (real-mode)
  ; powers of zero
  (check-equal? (Expt  0  0)  +nan.0)
  (check-equal? (Expt  0  1)    0)
  (check-equal? (Expt  0  2)    0)
  (check-equal? (Expt  0  2/3)  0)
  (check-equal? (Expt  0  2.)   0 ) ; floating points are contagious - but the first 0 is exact...
  (check-equal? (Expt  0. 2)    0.) ; floating points are contagious

  ; zero as exponent
  (check-equal? (Expt  1   0)    1)
  (check-equal? (Expt  2   0)    1)
  (check-equal? (Expt  2.  0)    1)
  (check-equal? (Expt  2/3 0)    1)  
  (check-equal? (Expt -1   0)    1)
  (check-equal? (Expt -2   0)    1)
  (check-equal? (Expt -2.  0)    1) 
  (check-equal? (Expt -2/3 0)    1)

  ; inexact zero as exponent
  (check-equal? (Expt  1   0.)   1)   ; 1^x is constant 1, so the result is exact
  (check-equal? (Expt  2   0.)   1.)
  (check-equal? (Expt  2.  0.)   1.)
  (check-equal? (Expt  2/3 0.)   1.)  
  (check-equal? (Expt -1   0.)   1.)
  (check-equal? (Expt -2   0.)   1.)
  (check-equal? (Expt -2.  0.)   1.)
  (check-equal? (Expt -2/9 0.)   1.)
  
  ; exact integers 
  (check-equal? (Expt  2  3)  8)
  (check-equal? (Expt -2  3) -8)
  (check-equal? (Expt -2 -3) -1/8)
  (check-equal? (Expt  2 -3)  1/8)

  
  (check-equal? (Expt 2/3 -1) 3/2)
  ; (check-equal? (Expt 4 -1/2) 1/2) ; nspire / maxima
  ; (check-equal? (Expt 8 1/3) 2.0)  ; mspire / maxima 
  (check-equal? (Exp (Ln 3)) 3)
  (check-equal? (Exp '(* 2 (ln x))) '(expt x 2)))

(define (Sqr: u)
  (Expt u 2))

(define-match-expander Sqr
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqr: u)] [_ (identifier? stx) #'Sqr:])))

; Also match u as (Expt u 1).
; Will not match (Expt u 0).
(define-match-expander GreedyExpt
  (λ (stx) (syntax-parse stx [(_ u v) #'(or (Expt u v) (and u (bind: v 1)))])))

(module+ test
  (displayln "TEST - GreedyExpt")
  (check-equal? (match 2 [(GreedyExpt u v) (list u v)]) '(2 1))
  (check-equal? (match (Exp 'a) [(GreedyExpt u v) (list u v)]) '(@e a)))

;;;
;;; Complex Expressions
;;;

;;; Imaginary Term

; A term of the form
;      @i        or
;   (* @i   u ...) or
;   (* @i r u ...)
; where r is a real numbers, is called an *imaginary term*.

(define (imaginary-term? u)
  ; we assume u is normalized, so we don't need to look at other
  ; factors besides the first one.
  (match u
    [(ImaginaryTerm u) #t]
    [_                 #f]))

(module+ test
  (displayln "TEST - imaginary-term?")
  (complex-mode)
  (check-equal? (imaginary-term?      '@i)    #t)
  (check-equal? (imaginary-term? '(* @i 2))   #t)
  (check-equal? (imaginary-term? '(* @i 2 x)) #t)
  (check-equal? (imaginary-term? '(* 2 @e))   #f)
  (check-equal? (imaginary-term? 42)          #f))


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
  (check-equal? (match x [(rx+s y r s) (list r s)][_ #f]) #f)
  (check-equal? (match y [(rx+s y r s) (list r s)][_ #f]) '(1 0))
  (check-equal? (match '(+ (* x y) z) [(rx+s x r s) (list r s)][_ #f]) '(y z))
  (check-equal? (match '(+ (* x y) z) [(rx+s y r s) (list r s)][_ #f]) '(x z))
  (check-equal? (match '(+ (* x y) z) [(rx+s z r s) (list r s)][_ #f]) '(1 (* x y))))
  
(define (Magnitude: u)
  (when debugging? (displayln (list 'Magnitude u)))
  (math-match u
    [@i   1]
    [@e  @e]
    [@pi @pi]
    [r #:when (negative? r) (- r)]
    [(Complex a b) (Sqrt (⊕ (Sqr a) (Sqr b)))]
    [_ `(magnitude ,u)]))

(define-match-expander Magnitude
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'magnitude u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Magnitude: u)] [_ (identifier? stx) #'Magnitude:])))


(module+ test
  (displayln "TEST - magnitude")
  (complex-mode)
  (check-equal? (Magnitude '@i)  1)
  (check-equal? (Magnitude '@pi) '@pi)
  (check-equal? (Magnitude '@e)  '@e)
  (check-equal? (Magnitude  42)  42)
  (check-equal? (Magnitude -42)  42)
  (check-equal? (Magnitude  42.) 42.)
  (check-equal? (Magnitude -42.) 42.)
  (check-equal? (Magnitude '(* @i  2)) 2)
  (check-equal? (Magnitude '(* @i -2)) 2)
  (check-equal? (Magnitude (normalize '(+ 1 @i))) (Sqrt 2))
  (check-equal? (normalize '(magnitude (+ @i x))) '(expt (+ 1 (expt x 2)) 1/2))
  ; check normalize knows magnitude
  (check-equal? (normalize '(magnitude 1)) 1))


(define (Angle: u)
  (when debugging? (displayln (list 'Angle u)))
  (math-match u
    [@i  (⊗ 1/2 @pi)]
    [@e  0]
    [@pi 0]
    [0   'error]
    [r #:when (> r 0) 0]
    [r #:when (< r 0) @pi]
    [(Complex a b) 
     (math-match* (a b)
                  [(r s) (define m (Sqrt (+ (sqr r) (sqr s))))
                         (cond
                           ; [(> r 0)                   (Atan (⊘ s r))]
                           ; real axis
                           [(and (= s 0) (> r 0))     0]
                           [(and (= s 0) (< r 0))     @pi]
                           ; image axis
                           [(and (= r 0) (> s 0))     '(*  1/2 @pi)]
                           [(and (= r 0) (< s 0))     '(* -1/2 @pi)]
                           ; Quadrants
                           [(and (> r 0) (> s 0))        (Acos (⊘    r  m))]      ; q1
                           [(and (< r 0) (> s 0)) (⊖ @pi (Acos (⊘ (- r) m)))]     ; q2
                           [(and (< r 0) (< s 0)) (⊖     (Acos (⊘ (- r) m)) @pi)] ; q3
                           [(and (> r 0) (< s 0)) (⊖     (Acos (⊘    r m)))]      ; q4
                           ; origo
                           [else                   'error])]
                  [(_ __) `(angle ,u)])]
    [_ `(angle ,u)]))

                                
(module+ test
  (displayln "TEST - Angle")
  (complex-mode)
  ; the axes
  (check-equal? (normalize '(angle  1))                        0)
  (check-equal? (normalize '(angle -1))                          @pi)
  (check-equal? (normalize '(angle       @i))           '(*  1/2 @pi))
  (check-equal? (normalize '(angle    (* @i -1)))       '(* -1/2 @pi))
  ; the quadrants
  (check-equal? (normalize '(angle (+    @i       1 ))) '(*  1/4 @pi)) ; q1
  (check-equal? (normalize '(angle (+    @i      -1 ))) '(*  3/4 @pi)) ; q2
  (check-equal? (normalize '(angle (+ (* @i -1 ) -1 ))) '(* -3/4 @pi)) ; q3
  (check-equal? (normalize '(angle (+ (* @i -1 )  1 ))) '(* -1/4 @pi)) ; q4
  
  (check-equal? (normalize '(angle (+  2 @i))) '(acos (* 2 (expt 5 -1/2)))))

(define-match-expander Angle
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'angle u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Angle: u)] [_ (identifier? stx) #'Angle:])))


(define (ExpI θ) (⊕ (Cos θ) (⊗ (Sin θ) @i)))
  

; Compute u=a+ib to v=c+id

(define (ComplexRealExpt a b c) ; d=0
  (when debugging? (displayln (list 'ComplexRealExpt a b c)))
  (math-match* (a b c)
    [(r1 r2 s)     
     (define r (Sqrt (⊕ (Sqr r1) (Sqr r2))))
     (define θ (if (> r2 0) (Acos (⊘ r1 r)) (Asin (⊘ r1 r))))
     #;(⊗ (Expt r s) (ExpI (⊗ θ s)))
     (⊕ (⊗    (Expt r s) (Cos (⊗ θ s)))  ; this form simplifies a bit more
        (⊗ @i (Expt r s) (Sin (⊗ θ s))))]
    [(a b c)
     `(expt ,(⊕ a (⊗ b @i)) ,c)]))

(define (RealComplexExpt r a b)
  (when debugging? (displayln (list 'RealComplexExpt r a b)))
  ; r^z = e^ln(r)^z = e^(z ln(r)) = e^((a+ib) ln(r)) 
  ;                               = e^(a ln(r)) * e^(i b ln(r))) = r^a * e^(i b ln(r)))
  (⊗ (Expt r a) (Exp (⊗ b @i (Ln r)))))

(define (ComplexComplexExpt a b c d)
  (when debugging? (displayln (list 'ComplexComplexExpt a b c d)))
  (math-match* (a b c d)
    [(r1 r2 s1 s2 )
     (cond
       [(and (= r1 0) (= r2 1)) ; i.e. i^(c+di)
        ; ^(c+*d) ▸   cos( ((c*π)/(2)) ) * ^(((−d*π)/(2)))
        ;             + sin( ((c*π)/(2)) ) * ^(((−d*π)/(2)))*
        (⊕ (⊗    (Cos (⊗ 1/2 @pi c)) (Exp (⊗ -1/2 d @pi)))
           (⊗ @i (Sin (⊗ 1/2 @pi c)) (Exp (⊗ -1/2 d @pi))))]

       [(= r1 0)
        ; (b*)^(c+*d) ▸     cos( ((ln(b^2)*d)/2) + ((sign(b)*c*π)/2) ) * (b^2)^(c/2) *^((−sign(b)*d*π)/2)
        ;                 + *sin(((ln(b^2)*d)/2 )+ ((sign(b)*c*π)/2) )* (b^2)^(c/)) *^((−sign(b)*d*π)/2)
        (define sign (if (> r2 0) +1 -1))
        (⊕ (⊗    (Cos (⊕  (⊗ 1/2 (Ln (Sqr b)) d) (⊗ (* sign 1/2) c @pi))) (Expt (Sqr b) (⊘ c 2))  (Exp (⊗ (* sign 1/2) d @pi)))
           (⊗ @i (Sin (⊕  (⊗ 1/2 (Ln (Sqr b)) d) (⊗ (* sign 1/2) c @pi))) (Expt (Sqr b) (⊘ c 2))  (Exp (⊗ (* sign 1/2) d @pi))))]
        
       [else
        ; (a+b*)^(c+d*) ▸   cos( ((ln(a^2+b^2)*d)/2) -(((2*tan(a/b)-sign(b)*π)*c)/(2)) )  *(a^(2)+b^(2))^(((c)/(2))) * ^(tan(((a)/(b)))*d-((sign(b)*d*π)/(2)))
        ;                 + i sin( ((ln(a^2+b^2)*d)/2) -(((2*tan(a/b)-sign(b)*π)*c)/(2)) )  *(a^(2)+b^(2))^(((c)/(2))) * ^(tan(((a)/(b)))*d-((sign(b)*d*π)/(2)))
        (define sign (if (> b 0) +1 -1))
        (define a^2+b^2 (⊕ (Sqr a) (Sqr b)))
        (define ln-a^2+b^2 (Ln a^2+b^2))
        (define arg  (⊖  (⊗ 1/2 ln-a^2+b^2 d) (⊖    (Atan (⊘ a b))    (⊗ (* sign 1/2) c @pi))))
        (define arg2                          (⊖ (⊗ (Atan (⊘ a b)) d) (⊗ (* sign 1/2) d @pi)))
        
        (define a^2+b^2-to-c/2 (Expt a^2+b^2 (⊘ c 2)))
        (⊕ (⊗    (Cos arg) a^2+b^2-to-c/2  (Exp arg2))
           (⊗ @i (Sin arg) a^2+b^2-to-c/2  (Exp arg2)))])]
       ; `(expt ,(⊕ r1 (⊗ r2 @i)) ,(⊕ s1 (⊗ s2 @i)))
    [(a b c d)
     `(expt ,(⊕ a (⊗ b @i)) ,(⊕ c (⊗ d @i)))]))


(module+ test
  (displayln "TEST - complex-expt-expand")
  (complex-mode)
  (check-equal? (Expt '@i  0)  1)
  (check-equal? (Expt '@i  1) '@i)
  (check-equal? (Expt '@i  2) -1)
  (check-equal? (Expt '@i  3) '(* @i -1))
  (check-equal? (Expt '@i  4)  1)
  
  (check-equal? (Expt '@i -1) '(* @i -1))
  (check-equal? (Expt '@i -2) -1)
  (check-equal? (Expt '@i -3) '@i)
  (check-equal? (Expt '@i -4)  1)

  (check-equal? (Expt '@i  1/2) '(+ (*  @i (expt 2 -1/2))        (expt 2 -1/2) ))
  (check-equal? (Expt '@i  1/3) '(+ (*  @i          1/2 ) (* 1/2 (expt 3  1/2)) ))
  (check-equal? (Expt '@i  1/4) '(+ (* @i (expt (* 1/2 (+ 1 (* -1 (expt 2 -1/2)))) 1/2))
                                          (expt (* 1/2 (+ 1       (expt 2 -1/2)))  1/2)))
  (check-equal? (Expt '@i  2/3)  '(+ (* @i 1/2 (expt 3 1/2)) 1/2))

  (check-equal? (Expt '(* @i 2) 0)  1)
  (check-equal? (Expt '(* @i 2) 1) '(* @i  2))
  (check-equal? (Expt '(* @i 2) 2) -4)
  (check-equal? (Expt '(* @i 2) 3) '(* @i -8))
  (check-equal? (Expt '(* @i 2) 4)  16)

  (check-equal? (Expt '(* @i 2) -1) '(* @i -1/2))
  (check-equal? (Expt '(* @i 2) -2) -1/4)
  (check-equal? (Expt '(* @i 2) -3) '(* @i 1/8))
  (check-equal? (Expt '(* @i 2) -4)  1/16)
  
  (check-equal? (Expt '(* @i 2) 1/2) '(+ @i 1))
  ; Actual: '(* (expt 2 1/2) (+ (expt 2 -1/2) (* (expt 2 -1/2) @i)))
  ;         which is correct mathematically
  
  (check-equal? (Expt '(* @i 2.) 0)  1)
  (check-equal? (Expt '(* @i 2.) 1) '(* @i 2.))
  (check-equal? (Expt '(* @i 2.) 2) -4.)
  (check-equal? (Expt '(* @i 2.) 3) '(* @i -8.))
  (check-equal? (Expt '(* @i 2.) 4)  16.)

  (check-equal? (Expt @i     @i)    '(expt @e (* -1/2 @pi)))
  (check-equal? (Expt @i '(* @i 2)) '(expt @e (* -1   @pi)))
  (check-equal? (Expt @i '(* @i 3)) '(expt @e (* -3/2 @pi)))
  (check-equal? (Expt @i '(* @i 4)) '(expt @e (* -2   @pi)))
  
  (check-equal? (Expt @i '(* @i -1)) '(expt @e (* 1/2 @pi)))
  (check-equal? (Expt @i '(* @i -2)) '(expt @e        @pi))
  (check-equal? (Expt @i '(* @i -3)) '(expt @e (* 3/2 @pi)))
  (check-equal? (Expt @i '(* @i -4)) '(expt @e (* 2   @pi)))

  (check-equal? (Expt @i '(* @i 1/2)) '(expt @e (* -1/4 @pi)))
  (check-equal? (Expt @i '(* @i 1/3)) '(expt @e (* -1/6 @pi)))
  (check-equal? (Expt @i '(* @i 1/4)) '(expt @e (* -1/8 @pi)))
  (check-equal? (Expt @i '(* @i 2/3)) '(expt @e (* -1/3 @pi)))
  
  (check-equal? (Expt '(+ @i 1)  1)  '(+ @i 1))
  (check-equal? (Expt '(+ @i 1)  2)  '(* @i 2)) 
  (check-equal? (Expt '(+ @i 1)  3)  '(+ (* @i 2) -2))
  (check-equal? (Expt '(+ @i 1)  4)  -4)

  ; The value of this one depends on, whether we are in real or complex mode.
  ; In real mode (-8)^(1/3)=-3 and in complex mode, the principal value is computed.
  (real-mode)
  (check-equal? (normalize '(expt -8 1/3)) -2)
  (complex-mode)
  (check-equal? (normalize '(expt -8 1/3)) '(* 2 (+ (* @i 1/2 (expt 3 1/2)) 1/2)))
  (check-equal? (N (normalize '(expt -8 1/3))) 1.0+1.7320508075688772i)
  
  
  (check-equal? 
   (normalize '(expt 1+i 1+i))
   '(+ (* @i (expt 2 1/2)  (expt @e (* -1/4 @pi)) (sin (+ (* 1/4 @pi) (* 1/2 (ln 2)))))
       (*    (expt 2 1/2)  (expt @e (* -1/4 @pi)) (cos (+ (* 1/4 @pi) (* 1/2 (ln 2)))))))
  
  (check-equal? (normalize '(exp (* @i @pi))) -1)
  (check-equal?
   (normalize '(expt 1+i 1-i))
   '(+ (* @i (expt 2 1/2) (expt @e (* 1/4 @pi)) (sin (+ (* 1/4 @pi) (* -1/2 (ln 2)))))
       (*    (expt 2 1/2) (expt @e (* 1/4 @pi)) (cos (+ (* 1/4 @pi) (* -1/2 (ln 2)))))))
  (check-= (N (normalize '(expt 1+i 1+i)))      (expt 1+i 1+i) 0.0001)
  (check-= (N (normalize '(expt 1+i 1-i)))      (expt 1+i 1-i) 0.0001)
  (check-= (N (normalize '(expt 1+i (+ @i 1)))) (expt 1+i 1+i) 0.0001))

(define (Ln: u)
  (when debugging? (displayln (list 'Ln: u)))
  (math-match u
    [1  0]
    ; [0  +nan.0] ; TODO: error?
    [r. #:when (%positive? r.)  (%ln r.)]
    [@e  1]
    [(Complex a b) #:when (not (equal? 0 b))
                   (⊕ (Ln (Sqrt (⊕ (Sqr a) (Sqr b)))) 
                      (⊗ @i (Angle (Complex a b))))]
    [(Expt @e v) v]
    [(Expt u α) #:when (= (%numerator (abs α)) 1)
                (⊗ α (Ln: u))]
    [(⊗ u v)  (⊕ (Ln: u) (Ln: v))]
    [_ `(ln ,u)]))

(define-match-expander Ln
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'ln u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Ln: u)] [_ (identifier? stx) #'Ln:])))

(module+ test
  (displayln "TEST - Ln")
  (check-equal? (Ln 1)  0)
  (check-equal? (Ln 1.) 0.)
  (check-equal? (Ln (bf 1)) 0.bf)
  (check-equal? (Ln @e) 1)
  (check-equal? (Ln (Exp 1.0)) 1.0)
  (check-true   (bf<  (bfabs (bf- (bflog (bfexp (bf 1))) (bf 1)))  (bfexpt (bf 10) (bf -30))))
  (check-equal? (Ln (Exp x)) x)
  (check-equal? (Ln (Expt (Exp x) 2)) '(* 2 x))
  (check-equal? (Ln (Expt x 3)) '(ln (expt x 3)))
  (check-equal? (Ln (⊗ 7 x (Expt y 3))) '(+ (ln 7) (ln x) (ln (expt y 3))))
  (check-equal? (Ln: (Expt x -1/2)) '(* -1/2 (ln x)))
  (check-equal? (Ln       @i)     '(* @i  1/2 @pi))
  (check-equal? (Ln (⊗ -1 @i))    '(* @i -1/2 @pi))
  (check-equal? (Ln (⊗  2 @i)) '(+ (* @i  1/2 @pi) (ln 2)))
  (check-equal? (Ln (⊕  1 @i)) '(+ (* @i  1/4 @pi) (* 1/2 (ln 2))))
  )


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
  (when debugging? (displayln (list 'Log: u v)))
  (math-match* (u v)
    [(_ #f)    (Log: 10 u)] ; 10 is the default base
    [(@e v)    (Ln: v)]     ; special case the natural logarithm
    [(_ 1)     0]
    ; [(_ 0)     +nan.0] ; TODO: error?
    [(1 u)     '<undefined:log-with-base-1-is-undefined>] ; TODO: error?
    [(n m) #:when (divides? n m) (let ([k (max-dividing-power n m)])
                                   (⊕ k (Log n (⊘ m (Expt n k)))))]
    [(n m) `(log ,n ,m)]
    [(2 r.0) #:when      (positive? r.0)              (fllog2 r.0)]
    [(r s)   #:when (and (positive? r) (positive? s)) (fllog10 r s)]

    [(10   r.bf) #:when (bfpositive? r.bf) (bflog10 r.bf)]
    [(2    r.bf) #:when (bfpositive? r.bf) (bflog2  r.bf)]
    [(r.bf s.bf) #:when (and (bfpositive? r.bf) (bfpositive? s.bf)) (bf/ (bflog r.bf) (bflog s.bf))]
    [(r    s.bf)  (Log: (bf r) s.bf)]
    [(r.bf s)     (Log: r.bf  (bf s))]
    
    [(u u)          1]
    [(u (Expt u v)) v]

    [(10 (⊗ u v))   (⊕ (Log: 10 u) (Log: 10 v))]
    
    ; [(n r.0) (log10 n r.0)]
    [(_ _)          `(log ,u ,v)]))

(define-match-expander Log
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'log u)] [(_ u v) #'(list 'log u v)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Log: u)] [(_ u v) #'(Log: u v)] [_ (identifier? stx) #'Log:])))

(module+ test
  (displayln "TEST - Log")
  (check-equal? (Log 2 1) 0)
  (check-equal? (Log 2 2) 1)
  (check-equal? (Log 2 4) 2)
  (check-equal? (Log 2 8) 3)
  (check-equal? (Log 2. 8.) 3.)
  (check-equal? (Log @e x) (Ln x))
  (check-equal? (Log 2 (Expt 2 x)) x))

; [0, 2)
(define (clamp-0-2 c)
  (let [(n (%numerator c)) (d (%denominator c))]
    (/ (modulo n (* 2 d)) d)))

; [-pi, pi), i.e [-1, 1)
; better be (-1, 1], but we can save the effort
; clamp-0-2(c + 1) - 1
(define (normalize-pi-coeff c)
  (- (clamp-0-2 (+ c 1)) 1))

(define (Cos: u)
  (when debugging? (displayln (list 'Cos: u)))
  (math-match u
    [0 1]
    [r.0 (cos r.0)]
    ; [r (cos r)] ; nope - automatic evaluation is for inexact results only
    [@pi -1]
    [(⊗ 1/3 @pi) 1/2]
    [(⊗ α u)   #:when (negative? α)      (Cos: (⊗ (- α) u))]  ; cos is even
    [(⊗ n @pi)                           (if (even? n) 1 -1)]    
    [(⊗ α @pi) #:when (integer? (* 2 α)) (cos-pi/2* (* 2 α))]
    [(⊗ α @pi) #:when (or (> α 1) (< α -1))
               (Cos (⊗ (normalize-pi-coeff α) @pi))]
    [(⊗ α @pi) #:when (> α 1/2) (⊖ (Cos (⊗ (- 1 α) @pi)))]
    [(⊗ α @pi) #:when (even? (%denominator α)) ; half angle formula
               (let ([sign (expt -1 (floor (/ (+ α 1) 2)))])
                 (⊗ sign (Sqrt (⊗ 1/2 (⊕ 1 (Cos (⊗ 2 α @pi)))))))] ; xxx test sign
    [(⊗ p (Integer _) @pi) #:when (even? p) 1]
    
    [(⊕ u (k⊗ p @pi)) #:when (odd? p)  (⊖ (Cos: u))]
    [(⊕ (k⊗ p @pi) u) #:when (odd? p)  (⊖ (Cos: u))]
    [(⊕ u (k⊗ p @pi)) #:when (even? p) (Cos: u)]
    [(⊕ (k⊗ p @pi) u) #:when (even? p) (Cos: u)]
    [(⊕ u (⊗ p (Integer _) @pi)) #:when (even? p) (Cos: u)]
    [(⊕ (⊗ p (Integer _) @pi) u) #:when (even? p) (Cos: u)]
    
    [(Acos u) u]    ; xxx only of -1<u<1
    [(Asin u) (Sqrt (⊖ 1 (Sqr u)))]
    [(Complex a b) #:when (not (zero? b)) (Cosh (⊗ @i u))]
    [(⊖ u) (Cos u)] ; even function    
    [_ `(cos ,u)]))

(define-match-expander Cos
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'cos u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Cos: u)] [_ (identifier? stx) #'Cos:])))

(module+ test
  (displayln "TEST - Cos")
  (check-equal? (Cos 0) 1)
  (check-equal? (Cos -3) (Cos 3))
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
  (check-equal? (Cos (⊕ x (⊗ 2 @p @pi))) (Cos x))
  (check-equal? (Cos (⊗ 4/3 @pi)) -1/2)
  (check-equal? (Cos (Acos x)) 'x)
  (check-equal? (Cos (Asin x)) (Sqrt (⊖ 1 (Sqr 'x))))
  (check-equal? (Cos @i) '(* 1/2 (+ (expt @e -1) @e))))

(define (Sin: u)
  (when debugging? (displayln (list 'Sin: u)))
  (define (Odd? n)  (and (integer? n) (odd? n)))
  (define (Even? n) (and (integer? n) (even? n)))
  (math-match u
    [0 0]
    [r.0 (sin r.0)]
    [@pi 0]
    [(⊗ 1/3 @pi) (⊘ (Sqrt 3) 2)]
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
    [(⊗ α @pi) #:when (or (> α 1) (< α -1))
               (Sin (⊗ (normalize-pi-coeff α) @pi))]
    [(⊗ α @pi) #:when (> α 1/2) (Sin (⊗ (⊖ 1 α) @pi))]
    [(⊗ α @pi) #:when (even? (%denominator α)) ; half angle formula
               (let* ([θ      (* 2 α pi)]
                      [sign.0 (sgn (+ (- (* 2 pi) θ) (* 4 pi (floor (/ θ (* 4 pi))))))]
                      [sign   (if (> sign.0 0) 1 -1)])
                 (⊗ sign (Sqrt (⊗ 1/2 (⊖ 1 (Cos (⊗ 2 α @pi)))))))] ; xxx find sign
    [(Asin u) u] ; only if -1<=u<=1   Maxima and MMA: sin(asin(3))=3 Nspire: error
    [(Acos u) (Sqrt (⊖ 1 (Sqr u)))]
    [(Complex a b) #:when (not (zero? b)) (⊗ @i -1 (Sinh (⊗ @i u)))]
    [(⊖ u) (⊖ (Sin u))] ; odd function
    [_ `(sin ,u)]))

(define-match-expander Sin
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'sin u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sin: u)] [_ (identifier? stx) #'Sin:])))

(module+ test 
  (displayln "TEST - Sin")
  (check-equal? (for/list ([n 8]) (Sin (⊗ n 1/2 @pi))) '(0 1 0 -1 0 1 0 -1))
  (check-equal? (Sin (⊖ x))              (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 2 @pi)))       (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 4 @pi)))       (Sin x))
  (check-equal? (Sin (⊕ x (⊗ -4 @pi)))      (Sin x))
  (check-equal? (Sin (⊕ x       @pi))    (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 3 @pi)))    (⊖ (Sin x)))
  (check-equal? (Sin (⊕ x (⊗ 2 @n @pi)))    (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 4 @n @pi)))    (Sin x))
  (check-equal? (Sin (⊕ x (⊗ 2 @p @pi)))    (Sin x))
  (check-equal? (Sin (⊗ 2/3 @pi)) '(* 1/2 (expt 3 1/2)))
  (check-equal? (Sin -3) (⊖ (Sin 3)))
  (check-equal? (Sin (Asin x)) 'x)
  (check-equal? (Sin (Acos x)) (Sqrt (⊖ 1 (Sqr x))))
  (check-equal? (Sin @i) '(* @i 1/2 (+ (* -1 (expt @e -1)) @e))))

(define (Tan u)
  (⊘ (Sin u) (Cos u)))

(define (Cot u)
  (⊘ (Cos u) (Sin u)))

(define (Csc u)
  (⊘ 1 (Sin u)))

(define (Sec u)
  (⊘ 1 (Cos u)))

(define (Cosh: u)
  (when debugging? (displayln (list 'Cosh: u)))
  (math-match u
    [0 1]
    [r.0 (cosh r.0)]
    [α #:when (negative? α) (Cosh: (- α))]
    [(ImaginaryTerm u) (Cos u)]
    [u (⊗ 1/2 (⊕ (Exp u) (Exp (⊖ u))))]))

(define (Sinh: u)
  (when debugging? (displayln (list 'Sinh: u)))
  (math-match u
    [0 0]
    [r.0  (sinh r.0)]
    [α #:when (negative? α) (⊖ (Sinh: (- α)))]
    [(ImaginaryTerm u) (⊗ @i (Sin u))]
    [u (⊗ 1/2 (⊖ (Exp u) (Exp (⊖ u))))]))

;;; Need to tune Cosh, Sinh.
(define-match-expander Cosh
  (λ (stx) (syntax-parse stx [(_ u) #'(or (list 'cosh u) (⊗ 1/2 (⊕ (Exp (⊖ u)) (Exp u))))]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Cosh: u)] [_ (identifier? stx) #'Cosh:])))

(define-match-expander Sinh
  (λ (stx) (syntax-parse stx [(_ u) #'(or (list 'sinh u) (⊗ 1/2 (⊖ (Exp u) (Exp (⊖ u)))))]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sinh: u)] [_ (identifier? stx) #'Sinh:])))

(define (double u)
  (⊗ 2 u))

(define-match-expander 2⊗Cosh
  (λ (stx) (syntax-parse stx [(_ u) #'(⊕ (Exp (⊖ u)) (Exp u))])))

(define-match-expander 2⊗Sinh
  (λ (stx) (syntax-parse stx [(_ u) #'(⊖ (Exp u) (Exp (⊖ u)))])))

(module+ test
  (displayln "TEST - Cosh")
  (check-equal? (N (subst (Cosh x) x 1)) (cosh 1))
  (check-equal? (N (subst (Sinh x) x 1)) (sinh 1))
  (check-equal? (match (Sinh x) [(Sinh y) y]) 'x)
  (check-equal? (match (Sinh x) [(⊗ 1/2 (2⊗Sinh y)) y]) x)
  (check-equal? (match (Cosh x) [(⊗ 1/2 (2⊗Cosh y)) y]) x)
  (check-equal? (match (⊗ 2 (Sinh x)) [(2⊗Sinh u) u]) x)
  (check-equal? (match (⊗ 2 (Cosh x)) [(2⊗Cosh u) u]) x))
  
(define (Asin: w)
  (when debugging? (displayln (list 'Asin: w)))
  (math-match w
    [0 0]
    [1  (⊗ 1/2 @pi)]
    [1/2 (⊗ 1/6 @pi)]
    [(list '* 1/2 (list 'expt 3 1/2))               (⊗ 1/3 @pi)]
    [(Expt 2 -1/2) (⊗ 1/4 @pi)]
    [(list '* 1/2 (list 'expt 2 1/2)) (⊗ 1/4 @pi)]
    [(⊖ u) (⊖ (Asin u))] ; odd function
    [r.0 (asin r.0)]
    [_ `(asin ,w)]))

(define-match-expander Asin
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'asin u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Asin: u)] [_ (identifier? stx) #'Asin:])))

; Acos = pi/2 - Asin
(define (Acos: w)
  (when debugging? (displayln (list 'Acos: w)))
  (math-match w
    [0 (⊘ @pi 2)]
    [1 0]
    [1/2 (⊗ 1/3 @pi)]
    [(list '* 1/2 (list 'expt 3 1/2))               (⊗ 1/6 @pi)]
    [(Expt 2 -1/2) (⊗ 1/4 @pi)]
    [(list '* 1/2 (list 'expt 2 1/2)) (⊗ 1/4 @pi)]
    [(⊖ u) (⊖ @pi (Acos u))]
    [r.0 (acos r.0)]
    [_ `(acos ,w)]))

(define-match-expander Acos
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'acos u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Acos: u)] [_ (identifier? stx) #'Acos:])))

(module+ test
  (displayln "TEST - Acos")
  (check-equal? (Acos -1/2) '(* 2/3 @pi))
  (check-equal? (Asin -1/2) '(* -1/6 @pi))
  (check-equal? (Acos '(* 1/2 (expt 3 1/2))) '(* 1/6 @pi))
  (check-equal? (Asin '(* 1/2 (expt 3 1/2))) '(* 1/3 @pi))
  (check-equal? (Asin (Sin '(* -1/3 @pi))) '(* -1/3 @pi))
  (check-equal? (Acos (Cos '(* -1/3 @pi))) '(* 1/3 @pi))
  (check-equal? (Asin (Sin '(* -1/6 @pi))) '(* -1/6 @pi))
  (check-equal? (Acos (Cos '(* -1/6 @pi))) '(* 1/6 @pi)))

(define (Atan: u)
  (when debugging? (displayln (list 'Atan: u)))
  (math-match u
    [r.0 (atan r.0)]
    [u   (Asin (⊘ u (Sqrt (⊕ 1 (Sqr u)))))]))

; Patterns involved with Atan should appear before Similar patterns with Asin to avoid being hijacked.
(define-match-expander Atan
  (λ (stx) (syntax-parse stx [(_ u) #'(or (list 'atan u) (Asin (⊘ u (Sqrt (⊕ 1 (Sqr u))))))]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Atan: u)] [_ (identifier? stx) #'Atan:])))

(define (Asec u)
  (Acos (⊘ 1 u)))

(define (Acsc u)
  (Asin (⊘ 1 u)))

(define (Tanh u)
  (⊘ (Sinh u) (Cosh u)))

(define (Atanh u)
  (⊗ 1/2 (⊕ (Ln (⊕ 1 u)) (Ln (⊖ 1 u)))))

(define (Asinh: u)
  (Ln (⊕ u (Sqrt (⊕ (Sqr u) 1)))))

(define-match-expander Asinh
  (λ (stx) (syntax-parse stx [(_ u) #'(or (list 'asinh u)
                                            (Ln (PlusTerms u (Sqrt (⊕ -1 (Sqr u))))))]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Asinh: u)] [_ (identifier? stx) #'Asinh:])))

(define (Acosh: u)
  (Ln (⊕ u (Sqrt (⊕ (Sqr u) -1)))))

(define-match-expander Acosh
  (λ (stx) (syntax-parse stx [(_ u) #'(or (list 'acosh u)
                                            (Ln (PlusTerms u (Sqrt (⊕ 1 (Sqr u))))))]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Acosh: u)] [_ (identifier? stx) #'Acosh:])))

(define (Sinc: u)
  (when debugging? (displayln (list 'Sinc: u)))
  (math-match u
    [0 1]
    [_ (⊘ (Sin u) u)]))

(define-match-expander Sinc
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'sinc u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sinc: u)] [_ (identifier? stx) #'Sinc:])))

(define (Si: u)
  (when debugging? (displayln (list 'Si: u)))
  (math-match u
    [0 0]
    [_ `(si ,u)]))

(define-match-expander Si
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'si u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Si: u)] [_ (identifier? stx) #'Si:])))

(define (Ci: u)
  (when debugging? (displayln (list 'Ci: u)))
  (math-match u
    [0 0]
    [_ `(ci ,u)]))

(define-match-expander Ci
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'ci u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Ci: u)] [_ (identifier? stx) #'Ci:])))

(define (Degree u)
  (⊗ (⊘ @pi 180) u))


(define (Sqrt: u)
  (Expt u 1/2))

(define-match-expander Sqrt
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 1/2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqrt: u)] [_ (identifier? stx) #'Sqrt:])))


(define (Abs: u)
  (math-match u
    [α   (if (< α   0) (- α)   α)]
    [r   (if (< r   0) (- r  ) r  )]
    [r.0 (if (< r.0 0) (- r.0) r.0)]
    [@e  @e]
    [@pi @pi]
    [@i 1]
    [_   `(abs ,u)]))

(define-match-expander Abs
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'abs u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Abs: u)] [_ (identifier? stx) #'Abs:])))

(module+ test 
  (check-equal? (Abs (⊕ x x)) (Abs (⊗ 2 x)))
  (check-equal? (Abs -42)   42)
  (check-equal? (Abs   0)    0)
  (check-equal? (Abs  42)   42)
  (check-equal? (Abs -42.0) 42.0)
  (check-equal? (Abs   0.0)  0.0)
  (check-equal? (Abs  42.0) 42.0))

(define (Root u n)
  (Expt u (⊘ 1 n)))

(module+ test
  (displayln "TEST - Sqrt")
  (check-equal? (Sqrt 0) 0) (check-equal? (Sqrt 1) 1) (check-equal? (Sqrt 4) 2))

(define (1/sqrt:1-u2 u)
  (⊘ 1 (Sqrt (⊖ 1 (Sqr u)))))

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
    [(Expt r y)  #:when (and (positive? r) (equal? y x))  (⊗ (Expt r x) (Ln r))]
    [(Expt u v)  (diff (Exp (⊗ v (Ln u))) x)] ; assumes u positive    
    ; [(Exp u)   (⊗ (Exp u) (d u))]
    [(Ln u)    (⊗ (⊘ 1 u) (d u))]
    [(Cos u)   (⊗ (⊖ 0 (Sin u)) (d u))]
    [(Sin u)   (⊗ (Cos u) (d u))]
    [(Asin u)  (1/sqrt:1-u2 u)]
    [(Acos u)  (⊖ (1/sqrt:1-u2 u))]
    [(Atan u)  (⊘ 1 (⊕ (Sqr x) 1))]
    [(Si x)    (Sinc x)]
    [(Ci x)    (⊘ (Cos x) x)]
    [(app: f us)  #:when (symbol? f)
                  (match us
                    [(list u) (cond [(eq? u x)  (Diff `(,f ,x) x)]
                                    [else       (⊗ `(app (deriviative ,f ,x) ,u) (d u))])] ; xxx
                    [_ `(diff (,f ,@us) ,x)])]           ; xxx
    [_ (error 'diff (~a "got: " u " wrt " x))]))

(define (Diff: u [x 'x])
  (define D Diff:)
  (math-match u
    [(Equal u1 u2) (Equal (D u1 x) (D u2 x))]
    [_             (list 'diff u x)]))

(define-match-expander Diff
  (λ (stx) (syntax-parse stx [(_ u x) #'(list 'diff u x)]))
  (λ (stx) (syntax-parse stx [(_ u x) #'(Diff: u)] [_ (identifier? stx) #'Diff:])))



(module+ test
  (displayln "TEST - diff")
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
  ; TODO: ASE should rewrite the result to (* '(expt x x) (+ 1 (ln x)))
  (check-equal? (diff (Expt x x) x) '(* (expt @e (* x (ln x))) (+ 1 (ln x))))
  (check-equal? (diff (Si x) x) (Sinc x))
  (check-equal? (diff (Ci x) x) (⊘ (Cos x) x))
  )

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
    [(Sum us) (filter non-free-of-x? us)]
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
  (check-equal? (extract-related-operands (⊗ (Exp x) x) x) '((expt @e x)))
  (check-equal? (extract-related-operands (⊗ (Expt x 5) x) x) '((expt x 3) x))
  (check-equal? (extract-related-operands (⊗ 3 (Sqr y)) y) '((expt y 2)))
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
      [(Sqrt (⊖ a2 (Sqr (== x)))) #:when (free-of-x a2)
                                  (try-subst-integrate u x (Asin (⊘ x (Sqrt a2))))]
      [(Sqrt (⊖ (Sqr (== x)) a2)) #:when (free-of-x a2)
                                  (try-subst-integrate u x (Asec (⊘ x (Sqrt a2))))]
      [(Sqrt (⊕ a2 (Sqr (== x)))) #:when (free-of-x a2)
                                  (try-subst-integrate u x (Atan (⊘ x (Sqrt a2))))]
      [(Sqrt (⊖ a2 (TimesTerms (Sqr (== x)) b2 ...))) #:when (andmap free-of-x (cons a2 b2))
                                                     (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                       (try-subst-integrate u x (Asin (⊗ x b/a))))]
      [(Sqrt (⊖ (TimesTerms (Sqr (== x)) b2 ...) a2)) #:when (andmap free-of-x (cons a2 b2))
                                                     (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                     (try-subst-integrate u x (Asec (⊗ x b/a))))]
      [(Sqrt (⊕ a2 (TimesTerms (Sqr (== x)) b2 ...))) #:when (andmap free-of-x (cons a2 b2))
                                                     (let* ([b (Sqrt (apply ⊗ b2))] [b/a (⊘ b (Sqrt a2))])
                                                     (try-subst-integrate u x (Atan (⊗ x b/a))))]
      [_ #f])))

(module+ test
  (displayln "TEST - trig-subst")
  (check-equal? (trig-subst '(expt (+ 1 (expt x 2)) 1/2) x '(expt (+ 1 (expt x 2)) 1/2)) (Atan x))
  (check-equal? (trig-subst '(expt (+ 1 (expt x 2)) -1/2) x '(expt (+ 1 (expt x 2)) 1/2))
                            '(+ (* 1/2 x (expt (+ 1 (expt x 2)) -1/2) (expt (+ 1 (* -1 (expt x 2) (expt (+ 1 (expt x 2)) -1))) 1/2))
                                (* 1/2 (asin (* x (expt (+ 1 (expt x 2)) -1/2))))))
  )
                
(define (try-subst-integrate u x v)
  (when debugging? (displayln (list 'try-subst-integrate u x v)))
  (define sym (gensym))
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
    [(integrate-table u x)]
    [(integrate-subst u x)]
    [(integrate-expand u x)]
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
  (check-equal? (integrate (⊘ 'C '(+ 'n (* -1 (expt x 2)))) x)
                '(* -2 C (expt (* -4 'n) -1/2) (asin (* 2 x (expt (* -4 'n) -1/2) (expt (+ 1 (* -1 (expt x 2) (expt 'n -1))) -1/2)))))
  (check-equal? (integrate (⊘ 'C '(expt (+ 'n (* -1 (expt x 2))) 1/2)) x)
                '(* C (expt 'n -1/2) (asin (* x (expt 'n -1/2))))) ; subst with tri funcs.
  (check-equal? (integrate (⊘ 'C '(+ 'A (* 'B (expt x 2)))) x)
                '(* 2 C (expt (* 4 'A 'B) -1/2) (asin (* 2 x (expt (* 4 'A 'B) -1/2) (expt (+ 1 (* (expt x 2) (expt 'A -1) 'B)) -1/2) 'B))))
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
  (check-equal? (integrate (Sqrt (Sqr x)) x) '(* (expt x 2) (piecewise (-1/2 (< x 0)) (1/2 (>= x 0)))))
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
  (check-equal? (limit (⊘ (⊖ (Sqr x) 1) (⊖ x 1)) x 1) 2)
  (check-equal? (limit (⊘ (⊖ (Sqr x) 4) (⊖ x 2)) x 2) 4))


;;; Piecewise 

(define (Piecewise: us vs) ; assume us and vs are canonical
  (define clauses
    ; simplify and remove clauses where the conditional is false
    (for/list ([u us] [v (map simplify vs)] #:when v)
      (list u v))) 
  ; if one of the conditional expressions v is true,
  ; then the result is the corresponding u.
  (define first-true    
    ; wrapped in list to disguish non-true and first true v has false u
    (let loop ([uvs clauses])      
      (match uvs
        ['()                     #f]
        [(list* (list u #t) uvs) (list u)]
        [_                       (loop (rest uvs))])))
  (match first-true
    [(list u) u]
    [_        (cons 'piecewise clauses)]))
        
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

;;; Numeric evalution

(define euler-e (exp 1))
(define imaginary-unit (sqrt -1))
; Given an expression without variables, N will evalutate the expression
; using Racket's standard mathematical operations.

(define (N u)
  (when debugging? (displayln (list 'N u)))
  (define (M  f F u)   (math-match (N u) [r (f r)] [v (F v)]))
  (define (M2 f F u v) (math-match* ((N u) (N v)) [(r s) (f r s)] [(v w) (F v w)]))
  (define (logical-or . xs)  (for/or  ([x xs]) (equal? x #t)))
  (define (logical-and . xs) (for/and ([x xs]) (equal? x #t)))

  (math-match u
    [r   r]
    [@pi pi]
    [@e  euler-e]
    [@i  imaginary-unit]
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
    [(Equal u v)        (M2 =  Equal u v)]
    [(Less u v)         (M2 <  Less u v)]
    [(LessEqual u v)    (M2 <= LessEqual u v)]
    [(Greater u v)      (M2 >  Greater u v)]
    [(GreaterEqual u v) (M2 >= GreaterEqual u v)]
    [(And u v)          (M2 logical-and And u v)]
    [(Or u v)           (M2 logical-or Or u v)]

    [(app: f us) `(,f ,@(map N us))]
    [_ u]))

(module+ test 
  (displayln "TEST - N")
  (check-equal? (N (subst '(expt (+ x 1) 5) x @pi)) (expt (+ pi 1) 5))
  (check-equal? (N '(expt @i 3)) (expt (expt -1 1/2) 3))
  (check-equal? (N (normalize '(= x (sqrt 2)))) (Equal x (sqrt 2))))

(module+ test
  (check-equal?   (normalize '(expt -8 1/3))  '(* 2 (+ (* @i 1/2 (expt 3 1/2)) 1/2)))
  ; only in complex mode
  ; (check-=     (N (normalize '(expt -8      1/3)))                 1+1.732i 0.0001) ; principal value 1+sqrt(3)i instead of 2i
  (check-=     (N (normalize '(expt -8+i -173/3))) (expt  -8+i -173/3) 0.0001)
  )

  
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
  ; Compute the first n+1 terms of the Taylor series of u
  ; wrt x around x=a. I.e. (taylor ... n) has degree n.
  (define (fact n) (if (<= n 0) 1 (* n (fact (- n 1)))))
  (define (terms u i)
    (cond [(> i n) 0]
          [else    (⊕ (⊗ (/ (fact i)) (subst u x a) (Expt (⊖ x a) i))
                      (terms (diff u x) (+ i 1)))]))
  (terms u 0))

(module+ test
  (displayln "TEST - taylor")
  (check-equal? (taylor '(sin x) x 0 5) '(+ x (* -1/6(expt x 3)) (* 1/120 (expt x 5))))
  #;(check-equal? (N (expand (taylor '(sin x) x 2 3)))
                  '(+ -0.6318662024609201 (* 2.2347416901985055 x) 
                      (* -0.8707955499599833 (expt x 2)) (* 0.0693578060911904 (expt x 3)))))

(define (free-of u v)
  ; return true if is not a complete subexpression of u, false otherwise
  (when verbose-debugging? (displayln (list 'free-of u v)))
  (define (f u)
    (and (not (equal? u v))
         (math-match u
           [r #t]
           [r.bf #t]
           [x #t]
           [(Piecewise us vs) (andmap f us)]
           [(app: _ us) (andmap f us)]
           [_ (error 'missing-case (~a "free-of:" u x))])))
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
  (when verbose-debugging? (displayln (list 'coefficient u v 'n n)))
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
  (displayln "TEST - part")
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

;;;
;;; Relational Operators
;;;

(define-match-expander Equal
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Equal: u v)] [_ (identifier? stx) #'Equal:])))

(define-match-expander Less
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '< u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Less: u v)] [_ (identifier? stx) #'Less:])))

(define-match-expander LessEqual
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '<= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(LessEqual: u v)] [_ (identifier? stx) #'LessEqual:])))

(define-match-expander Greater
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '> u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Greater: u v)] [_ (identifier? stx) #'Greater:])))

(define-match-expander GreaterEqual
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '>= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(GreaterEqual: u v)] [_ (identifier? stx) #'GreaterEqual:])))


(define (Equal:        u v) (math-match* (u v) [(r s) (=  r s)] [(_ __) `(=  ,u ,v)]))
(define (Less:         u v) (math-match* (u v) [(r s) (<  r s)] [(_ __) `(<  ,u ,v)]))
(define (LessEqual:    u v) (math-match* (u v) [(r s) (<= r s)] [(_ __) `(<= ,u ,v)]))
(define (Greater:      u v) (math-match* (u v) [(r s) (>  r s)] [(_ __) `(>  ,u ,v)]))
(define (GreaterEqual: u v) (math-match* (u v) [(r s) (>= r s)] [(_ __) `(>= ,u ,v)]))


(define-match-expander Or
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'or u v) (list-rest 'or u (app (λ(ys) (cons 'or ys)) v)))]
      [(_ u)       #'(list 'or u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(Or: u ...)] [_ (identifier? stx) #'Or:])))


(define (Or: . us)
  (match us
    ['() #f]
    [_  (let/ec return
          (define (flatten us)
            (reverse 
             (for/fold ([vs '()])
                       ([u (in-list us)])
               (match u
                 [#t             (return #t)]
                 [#f             vs]
                 [(list* 'or ws) (append vs (map flatten ws))]
                 [_              (cons u vs)]))))
          (match (remove-duplicates (flatten us))
            ['()        #f]
            [(list v)   v]
            [vs         `(or ,@(sort vs <<))]))]))
      

(module+ test 
  (check-equal? (normalize '(or (= x 3) (or (= x 2) (= x 1)))) '(or (= x 1) (= x 2) (= x 3)))
  (check-equal? (normalize '(or (= x 1) (= x 2) (= x 1))) '(or (= x 1) (= x 2))))

(define-match-expander And
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'and u v) (list-rest 'and u (app (λ(ys) (cons 'and ys)) v)))]
      [(_ u)       #'(list 'and u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(And: u ...)] [_ (identifier? stx) #'And:])))

(define (And: . us)
  (match us
    ['() #t]
    [_  (let/ec return
          (define (flatten us)
            (reverse 
             (for/fold ([vs '()]) ([u (in-list us)])
               (match u
                 [#t              vs]
                 [#f              (return #f)]
                 [(list* 'and ws) (append vs (map flatten ws))]
                 [_               (cons u vs)]))))
          (match (remove-duplicates (flatten us))
            ['()        #t]
            [(list v)   v]
            [vs         `(and ,@(sort vs <<))]))]))

(module+ test 
  (check-equal? (normalize '(and (= x 3) (and (= x 2) (= x 1)))) '(and (= x 1) (= x 2) (= x 3)))
  (check-equal? (normalize '(and (= x 1) (= x 2) (= x 1))) '(and (= x 1) (= x 2))))

; Tuples (aka column vectors)
(define-match-expander Up
  (λ (stx) (syntax-parse stx [(_ u ...) #'(list 'up u ...)]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(Up:      u ...)] [_ (identifier? stx) #'Up:])))

(define (Up: . us)  
  `(up ,@us))

(module+ test
  (check-equal? (Up 2 3) '(up 2 3)))

; Tuple indices are zero based
(define-match-expander Ref
  (λ (stx) (syntax-parse stx [(_ u i) #'(list 'ref u i)]))
  (λ (stx) (syntax-parse stx [(_ u i) #'(Ref:      u i)] [_ (identifier? stx) #'Ref:])))

(define (Ref: u i)
  (cond
    [(natural? i) (match u
                    [(Up us ...) (if (< i (length us)) (list-ref us i) `(ref ,u ,i))])]
    [else `(ref ,u ,i)]))

(module+ test
  (check-equal? (Ref (Up 2 3) 0) 2)
  (check-equal? (Ref (Up 2 3) 1) 3))

; Tuple indices are zero based
(define-match-expander Compose
  (λ (stx) (syntax-parse stx [(_ u v) #'(list 'compose u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Compose:      u v)] [_ (identifier? stx) #'Compose:])))

(define (Compose: u v)
  `(compose ,u ,v))

(module+ test
  (displayln "TEST - Compose")
  (check-equal? (Compose 'f 'g) '(compose f g)))


; Application
(define-match-expander App
  (λ (stx) (syntax-parse stx [(_ u ...) #'(list 'app u ...)]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(App:      u ...)] [_ (identifier? stx) #'App:])))

(define (App: u . us)
  (match u
    [(list 'up coords ...) `(up ,@(for/list ([coord coords]) (apply App: coord us)))]
    [(list 'compose u v)   (match us
                             [(list w) (App u (App v w))]
                             [_        `(app ,u ,@us)])]                              
    [_                     `(app ,u ,@us)]))

#;(define (Positive?: u)
    (math-match u
      [r      (positive? r)]
      [r.bf   (bfpositive? r.bf)]
      [(⊖ u)  #f]
      [_      #t])) ; todo: add cases for variables with assumptions

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
          [(Equal (Atan u) v) (r (Equal u (Tan v)))] ; Atan must be before Asin pattern. Asin pattern covers Atan.   
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
                [(⊗ v w) (solve1 (Equal (⊗ v w) 0))]
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
;;; FORMATTING
;;;

;;; Variables and Constants

; The parameter output-variable-name holds the formatter
; for variables and constants.

; Input  Default   TeX           MMA
; @e     e         \mathrm{e}    E
; @pi    pi        π             Pi
; @i     i         o             I
; x      x         x             x

; TeX handles various other symbols in symbol->tex.

(define (default-output-variable-name x)
  (match x ['@pi "pi"] ['@i "i"] ['@e "e"]           [_ (~a x)]))
(define (mma-output-variable-name x)
  (match x ['@pi "Pi"] ['@i "I"] ['@e "E"]           [_ (~a x)]))
(define (tex-output-variable-name x)
  (match x ['@pi "π"]  ['@i "i"] ['@e "\\mathrm{e}"] [_ (symbol->tex x)]))

;;; Fractions

(define (default-output-fraction α) (~a α))
(define (mma-output-fraction     α) (~a α))
(define (tex-output-fraction     α) 
  (if (> (denominator α) 1)
      (~a "\\frac{" (numerator α) "}{" (denominator α) "}")
      (~a α)))

;;; Roots

; If output-root? is true, the formatter uses output-root to output
; powers of the form (expt u 1/n).

(define (default-output-root u n)
  ; note: KAS can't parse root(u,n) so we need to output u^(1/n)
  #f) ; this makes verbose! output u^(1/n) with correct parens

;; (define (mma-output-root formatted-u) 
;;   (match u
;;     [(Expt u α) #:when (= (numerator? α) 1) (def n (/ 1 α)) (~a "Power[" formatted-u "," α ")")]
;;     [_ (error 'mma-output-root (~a "Expected expression of the form (expt u 1/n), got: " u))]))

;; (define (tex-output-root formatted-u) 
;;   (match u
;;     [(Expt u α) #:when (= (numerator? α) 1)  (def n (/ 1 α)) (~a "\\sqrt[" n " ]{" formatted-u "}")]
;;     [_ (error 'tex-output-root (~a "Expected expression of the form (expt u 1/n), got: " u))]))


;;; Logarithms

; Input      Default    Tex          MMA
; (log x)    log(x)     \log(x)      log(x)
; (log 2 x)  log_2(x)   \log_{2}(x)  log_2(x) 

(define (default-output-log u [v #f])
  (match-define (list l r) (output-application-brackets))
  (cond [v    (~a "log_" (verbose~ u) l (verbose~ v) r)]
        [else (~a "log" l (verbose~ u) r)]))

(define (default-output-up u v)
  (~a "(" (verbose~ u) "," (verbose~ v) ")"))


(define mma-output-log default-output-log)

(define (tex-output-log u [v #f])
  (parameterize ([output-wrapper values])
    (cond [v    (~a "\\log_{" (verbose~ u) "}(" (verbose~ v) ")")]
          [else (~a "\\log(" (verbose~ u) ")")])))

(define (tex-output-up u v)
  (parameterize ([output-wrapper values])
    (define x (verbose~ u))
    (define y (verbose~ v))
    (~a "\\begin{pmatrix} " x "\\\\" y "\\end{pmatrix}")))


;;; Formatting Parameters

(define output-application-brackets      (make-parameter (list "(" ")")))
(define output-format-function-symbol    (make-parameter ~a))
(define output-format-quotient           (make-parameter #f)) ; #f means default u/v
(define output-format-quotient-parens    (make-parameter (list "(" ")"))) 
(define output-sub-expression-parens     (make-parameter (list "(" ")")))
(define output-wrapper                   (make-parameter values))
(define output-use-quotients?            (make-parameter #t))
(define output-sqrt?                     (make-parameter #t)) ; use sqrt to output (expt u 1/2) ; otherwise as expt
(define output-root?                     (make-parameter #t)) ; use root to output (expt u 1/n) ; otherwise as expt
(define output-format-abs                (make-parameter (λ(u)   (~a "abs("  (verbose~ u) ")"))))
(define output-format-sqrt               (make-parameter (λ(u)   (~a "sqrt(" (verbose~ u) ")"))))
(define output-format-root               (make-parameter default-output-root))
(define output-format-log                (make-parameter default-output-log))
(define output-format-up                 (make-parameter default-output-up))
(define output-sub-exponent-parens       (make-parameter (list "(" ")"))) ; for Tex it is { }
(define output-sub-exponent-wrapper      (make-parameter values))         ; TeX needs extra {}
(define output-terms-descending?         (make-parameter #f)) ; reverse terms before outputting?
(define output-implicit-product?         (make-parameter #f)) ; useful for TeX
(define output-relational-operator       (make-parameter ~a)) ; useful for TeX
(define output-floating-point-precision  (make-parameter 4))  ; 
(define output-variable-name             (make-parameter default-output-variable-name)) ; also handles @e, @pi and @i
(define output-differentiation-mark      (make-parameter '(x))) ; use (u)' rather than d/dx(u) for variables in this list
(define output-fraction                  (make-parameter default-output-fraction))

(define (use-mma-output-style)
  (output-application-brackets (list "[" "]"))
  (output-format-function-symbol (λ(s) (string-titlecase (~a s))))
  (output-format-quotient #f)
  (output-format-quotient-parens (list "(" ")"))
  (output-sub-expression-parens  (list "(" ")"))
  (output-wrapper values)
  (output-sqrt? #t)
  (output-format-abs  (λ(u)   (~a "Abs["  (verbose~ u) "]")))
  (output-format-sqrt (λ(u)   (~a "Sqrt[" (verbose~ u) "]")))
  (output-format-root (λ(u n) (~a "Root[" (verbose~ u) "," (verbose~ n) "]")))
  (output-format-log mma-output-log)
  (output-format-up           default-output-up)
  (output-sub-exponent-parens (list "(" ")"))
  (output-sub-exponent-wrapper values)
  (output-implicit-product? #f)
  (output-relational-operator ~a)
  (output-variable-name mma-output-variable-name)
  (output-fraction mma-output-fraction))

(define (use-default-output-style)
  (output-application-brackets (list "(" ")"))
  (output-format-function-symbol ~a)
  (output-format-quotient #f)
  (output-format-quotient-parens (list "(" ")"))
  (output-sub-expression-parens  (list "(" ")"))
  (output-sub-exponent-parens    (list "(" ")"))
  (output-sub-exponent-wrapper   values)
  (output-wrapper values)
  (output-sqrt? #t)
  (output-root? #f)
  (output-format-abs  (λ(u)   (~a "abs("  (verbose~ u) ")")))
  (output-format-sqrt (λ(u)   (~a "sqrt(" (verbose~ u) ")")))
  (output-format-root (λ(u n) (~a "root(" (verbose~ u) "," (verbose~ n) ")")))
  (output-format-log default-output-log)
  (output-format-up  default-output-up)
  (output-implicit-product? #f)
  (output-relational-operator ~a)
  (output-variable-name default-output-variable-name)
  (output-fraction default-output-fraction))

(define (use-tex-output-style)
  (define operators '(sin cos tan log ln sqrt det))
  (define (~relop u)
    (match u
      ['<=  "≤ "]
      ['>=  "≥ "]
      ['~   "\\sim "]
      [_    (~a u)]))
  (define (~symbol s) 
    (match s
      ['acos "\\cos^{-1}"]
      ['asin "\\sin^{-1}"]
      ['atan "\\tan^{-1}"]
      [_ #:when (member s operators) (~a "\\" s)]
      ['<=  "\\leq "]
      ['>=  "\\geq "]
      ['~   "\\sim "]
      ['*   "\\cdot "]
      ['or  "\\vee "]
      ['and "\\wedge "]
      [_  (~a s)]))
  (output-application-brackets (list "(" ")"))
  (output-format-function-symbol ~symbol)
  (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
  (output-format-quotient-parens (list "" "")) ; not needed due to {} from \frac
  ; (output-use-quotients? #t)
  (output-sub-expression-parens (list "{" "}"))
  (output-wrapper (λ (s) (~a "$" s "$")))
  (output-format-abs  (λ(u)   (parameterize ([output-wrapper values])
                                (~a "\\left|"  (verbose~ u) "\\right|"))))  
  (output-sqrt? #t)
  (output-root? #f)
  (output-format-sqrt (λ(u)   (parameterize ([output-wrapper values])
                                (~a "\\sqrt{"  (verbose~ u) "}"))))  
  (output-format-root (λ(u n) (parameterize ([output-wrapper values])
                                (if (equal? n 2)
                                    (~a "\\sqrt{" (verbose~ u) "}")
                                    (~a "\\sqrt[" (verbose~ n) "]{" (verbose~ u) "}")))))
  (output-format-log tex-output-log)
  (output-format-up  tex-output-up)
  (output-sub-exponent-parens  (list "{" "}"))
  (output-sub-exponent-wrapper (λ (s) (~a "{" s "}")))
  (output-implicit-product? #t)
  (output-relational-operator ~relop)
  (output-variable-name tex-output-variable-name)
  (output-fraction tex-output-fraction))

(define (tex u)
  (define operators '(sin  cos  tan log ln sqrt
                           det
                      sinh cosh tanh )) ; needs \\ in output
  (define relational-operators '(= < <= > >=))
  (define (~relop u)
    (match u
      ['<=  "≤ "]
      ['>=  "≥ "]
      ['~   "\\sim "]
      [_    (~a u)]))
  (define (~symbol s)
    (match s
      ['acos "\\cos^{-1}"]
      ['asin "\\sin^{-1}"]
      ['atan "\\tan^{-1}"]
      [_ #:when (member s operators) (~a "\\" s)]      
      ['<=  "\\leq "]
      ['>=  "\\geq "]
      ['~   "\\sim "]
      ['*   "\\cdot "]   ; multiplication
      ['or  "\\vee "]    ; logical or
      ['and "\\wedge "]  ; logical and
      ['|%| "\\%"]
      [_  (~a s)]))
  (parameterize ((output-application-brackets (list "(" ")"))
                 (output-format-function-symbol ~symbol)
                 (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
                 (output-format-quotient-parens (list "" ""))
                 ; (output-use-quotients? #t)
                 (output-sub-expression-parens (list "{" "}"))
                 (output-wrapper (λ (s) (~a "$" s "$")))
                 ; (output-sqrt? #t) ; uncommented!! otherwise the user can't control it
                 (output-format-sqrt (λ(u) (parameterize ([output-wrapper values])
                                             (~a "\\sqrt{" (verbose~ u) "}"))))
                 (output-format-root (λ(u n) (parameterize ([output-wrapper values])
                                               (if (equal? n 2)
                                                   (~a "\\sqrt{" (verbose~ u) "}")
                                                   (~a "\\sqrt[" (verbose~ n) "]{" (verbose~ u) "}")))))
                 (output-sub-exponent-parens  (list "{" "}"))
                 (output-sub-exponent-wrapper (λ (s) (~a "{" s "}")))
                 (output-implicit-product?    #t)
                 (output-relational-operator  ~relop)
                 (output-variable-name        tex-output-variable-name)
                 (output-format-log           tex-output-log)
                 (output-format-up            tex-output-up)
                 (output-fraction             tex-output-fraction))
    (verbose~ u)))

(define char->tex
  (let ()
    (define dict
      ( hash
       ; symbolic constants
       'α "\\alpha"   'β "\\beta"    'γ "\\gamma"   'Γ "\\Gamma" 'δ "\\delta" 'Δ "\\Delta"
       'ε "\\epsilon" 'ζ "\\zeta"    'η "\\eta"     'θ "\\theta" 'Θ "\\Theta" 'ι "\\iota"
       'κ "\\kappa"   'λ "\\lambda"  'Λ "\\Lambda"  'μ "\\mu"    'ν "\\nu"    'ξ "\\xi"
       'Ξ "\\Xi"      'π "\\pi"      'Π "\\Pi"      'ρ "\\rho"   'σ "\\sigma" 'Σ "\\Sigma"
       'τ "\\Tau"     'υ "\\upsilon" 'Υ "\\Upsilon" 'φ "\\phi"   'Φ "\\Phi"   'χ "\\chi"
       'ψ "\\psi"     'Ψ "\\Psi"     'ω "\\omega"   'Ω "\\Omega" 
       '|%| "\\%"))
    (λ (c)
      (define s (string->symbol (string c)))
      (match (hash-ref dict s #f)
        [#f (string c)]
        [s  (~a s " ")]))))

(define (string->tex s)
  (define s1 (string-append* (map char->tex (string->list s))))
  (if (equal? s s1) s s1))

(define (symbol->tex s)
  (define t (string->symbol (string->tex (symbol->string s))))
  (match t
    ['@e  "\\mathrm{e}"]  ; Euler's constant
    ['@pi "\\pi"]         ; pi
    ['@i  "i"]            ; the imaginary unit
    ['@n  "@n"]           ; an arbitrary natural number
    ['@p  "@p"]           ; an arbitrary integer
    ['|%|  "\\%"]         ; an arbitrary integer
    
    [_ t]))


(define (prepare-unnormalized-for-formatting
         u
         #:zero-term   [zero-term   #f]  ; remove  0 in sums
         #:one-factor  [one-factor  #f]  ; rewrite (* 1 u) to u
         #:zero-factor [zero-factor #f]  ; rewrite (* 0 u) to 0
         #:all         [all         #t])
  ; the purpose of this function is to reuse the formatter for normalized
  ; expressions, for formatting unnormalized expressions.
  (when all
    (set! zero-term   #t)
    (set! one-factor  #t)
    (set! zero-factor #t))


  ;; Note: Differences and quotients does not appear in normalized expressions.
  ;;       Therefore we need to handle these with care.

  ;; The pattern ⊖ matches various differences
  ;;  (⊖ x y) matches (- a b)       and binds x->a, y->b
  ;;  (⊖ x y) matches (- a b c ...) and binds x->a, y->(+ b c ...)
  (define-match-expander ⊖
    (λ (stx)
      (syntax-parse stx
        [(_ u v) #'(or (list '- u v)
                       (list-rest '- u (app (λ(ys) (cons '+ ys)) v)))]
        [(_ u)       #'(list '- u)])))

  ;; The pattern ⊘ matches quotient
  ;;  (⊘ x y) matches (/ a b)       and binds x->a, y->b
  (define-match-expander ⊘
    (λ (stx)
      (syntax-parse stx
        [(_ u v) #'(list '/ u v)])))

  (define (argcons op u v)
    (match v
      [(list* (== op) vs) (list* op u vs)]
      [v                  (list  op u v)]))
  
  (define (p u)
    ; (displayln (list 'p u))
    (define (non-zero? u) (not (equal? 0 u)))
    (math-match u
     ; keep formatting declaration unchanged           
     [(list 'formatting options u)  `(formatting ,options ,(p u))]
     ; rewrites
     [(⊗ 1 v)         #:when one-factor (p v)]
     [(⊘ u 1)         #:when one-factor (p u)]
     [(⊗ 0 v)         #:when zero-factor 0]
     [(⊗ v 0)         #:when zero-factor 0]
     [(⊕ 0 v)         #:when zero-term  (p v)]
     [(⊕ v 0)         #:when zero-term  (p v)]
     [(⊕ (⊗ 0 u) v)   #:when zero-term  (p v)]
     [(⊕ (⊗ u 0) v)   #:when zero-term  (p v)]
     ; note: the above special cases a 0 as the second factor
     ;       a zero as third fact results in a zero term
     [(⊖ u 0)         #:when zero-term  (p u)]
     ; no rewrites
     [r               u]
     [r.bf            u]
     [x               u]
     ; rewrite sub expressions
     [(⊖ u)           (list     '- (p u)      )]
     [(⊖ u v)         (argcons  '- (p u) (p v))] 
     [(⊘ u v)         (list     '/ (p u) (p v))]  ; binary only     
     [(⊗ u v)         (argcons  '* (p u) (p v))]
     [(⊕ u v)         (match (list (p u) (p v))
                        [(list 0 0) 0]
                        [(list 0 u) u]
                        [(list u 0) u]
                        [(list u v) (argcons  '+ u v)])]
     [(⊕ u)           (p u)]
     
     ; other
     [(And   u v)     (argcons 'and (p u) (p v))]
     [(Or    u v)     (argcons 'or  (p u) (p v))]
     [(Equal u v)     (list    '=    (p u) (p v))]
     [(Expt  u v)     (list    'expt (p u) (p v))]
     [(Log   u)       (list    'log  (p u))]
     [(Log   u v)     (list    'log  (p u) (p v))]
     [(Piecewise us vs) (Piecewise: (map p us) (map p vs))]
     [(app: f us)     (cons f (map p us))]
     [_ (display u)
        (error 'prepare-unnormalized-for-formatting
               (~a "internal error, got: " u))]))
  (if (string? u)
      u
      (p u)))

(define prepare prepare-unnormalized-for-formatting)

; ~ converts an expression into a string
;  Originally it only formatted normalized expressions, but
;  now unnormalized expressions are supported too.
;  The output format is configured using parameters.
;  The three builtin styles are default, mma and tex.
(define (verbose~ u)
  ; (displayln u)
  (match-define (list app-left  app-right)  (output-application-brackets))
  (match-define (list sub-left  sub-right)  (output-sub-expression-parens))
  (match-define (list expt-left expt-right) (output-sub-exponent-parens))
  (match-define (list quot-left quot-right) (output-format-quotient-parens))
  ;(define use-quotients? (output-use-quotients?))
  (define ~sym (let ([sym (output-format-function-symbol)]) (λ (x) (sym x)))) ; function names
  (define ~var (let ([out (output-variable-name)]) (λ(x) (out x)))) ; variable names
  (define (~relop x) ((output-relational-operator) x))
  (define (~red str)  (~a "{\\color{red}" str "\\color{black}}"))
  (define (~blue str) (~a "{\\color{blue}" str "\\color{black}}"))
  (define (~explicit-paren strs) (~a "{\\left(" (string-append* (add-between strs ",")) "\\right)}"))

  (define (v~ u [original? #f])
    ; (displayln (list 'v~ u))
    (define ~frac (output-fraction))
    (define (~num r)
      (define precision (output-floating-point-precision))
      (cond [(and (exact? r) (> (denominator r) 1)) (~frac r)]
            [(exact? r) (~a r)]
            [(nan? r)   (~a r)]
            [precision  (~r r #:precision precision)]
            [else       (~a r)]))
    (define (paren u) ; always wrap in ( )
      (~a "(" (v~ u #t) ")"))
    (define (exponent-wrap s)
      (~a expt-left s expt-right))
    (define (sub u) ; always wrap in sub-left and sub-right parentheses
      (~a sub-left (v~ u #t) sub-right))    
    (define (exponent-sub u) ; wraps the exponent of an expt-expression
      (exponent-wrap (v~ u #t)))
    (define (base-sub u) ; wraps the base of an expt-expression
      (if (and (number? u) (negative? u))
          ; we only need to add real parens, if expt-left aren't (
          (if (equal? expt-left "(")
              (~a expt-left (v~ u) expt-right)
              (~a expt-left (paren u) expt-right))
          (if (equal? expt-left "(")
              (~a expt-left (v~ u) expt-right)
              (~a expt-left (paren u) expt-right))))
    (define (quotient-sub u) ; wraps numerator or denominator of quotient
      (~a quot-left (v~ u) quot-right))
    (define implicit-mult (if (output-implicit-product?) "" (~sym '*)))
    (define (argcons op x xs)
      (match xs
        [(list* (== op) args) (list* op x args)]
        [args                 (list* op x (list args))]))
    (define (implicit* u v) ; returns either (~sym '*) or implicit-mult
      (math-match u
        [r (math-match v
             [s                    (~sym '*)]
             [x                     implicit-mult]
             [(⊗ u1 u2)            (implicit* r u1)]
             [(Expt u1 u2)         (implicit* r u1)]
             [(list '+ u1 u2 ...)   implicit-mult]
             [(list 'vec u1 u2 ...) implicit-mult]  
             [_                   (~sym '*)])]        
        [_ (~sym '*)]))

    (define (prefix-minus s)
      (if (eqv? (string-ref s 0) #\-)
          (~a "-(" s ")")
          (~a "-" s)))
             
    (define (par u #:use [wrap paren] #:wrap-fractions? [wrap-fractions? #f]
                 #:exponent-base? [exponent-base? #f]) ; wrap if (locally) necessary
      (when debugging? (displayln (list 'par u 'orig original? 'exponent-base exponent-base?)))
      (math-match u
        [(list 'red   u) (~red  (par u))]           ; red color
        [(list 'blue  u) (~blue (par u))]           ; blue color
        [(list 'paren u ...) (~explicit-paren (map v~ u))] ; explicit parens (tex)
        [α    #:when (and wrap-fractions? (not (integer? α))) (wrap (~frac α))] ; XXX
        [α    #:when (not (integer? α)) (~frac α)] ; XXX
        [r    #:when (>= r 0)           (~num r)]
        [r.bf #:when (bf>= r.bf (bf 0)) (~a r.bf)]
        [x                              (~a (~var x))]
        ; infix operators and relations
        ; [(⊗ 1 v)     (exponent-wrap (par v))] ; xxx
        [(⊗  1 v)                       (exponent-wrap        (~a  (v~ v original?)))]
        [(⊗ -1 v) #:when exponent-base? (exponent-wrap        (~a "(-"        (v~ v #t) ")"))]
        [(⊗ -1 v) #:when original?      (let ([s (prefix-minus (v~ v))])
                                          (if (eqv? (string-ref s 0) #\-) (wrap s) (exponent-wrap s)))] ; XX
        [(⊗ -1 v)                       (exponent-wrap        (~a "(-"        (v~ v #t) ")"))]
        [(⊗ u v) #:when exponent-base?  (exponent-wrap (paren (~a (par u) (~sym '*) (par v))))] ; TODO XXX ~ two layers
        [(⊗ u v) #:when original?       (let ([s (~a      (v~ u)  (~sym '*) (par v))])
                                          (if (eqv? (string-ref s 0) #\-) (wrap s) (exponent-wrap s)))] ; XXX
        [(⊗ u v)                        (exponent-wrap (~a (par (v~ u)) (~sym '*) (par v)))]
        [(⊕ _ __)    (wrap u)]
        [(list* '- _ __) (wrap u)]
        [(And u v)   (~a (par u) " " (~sym 'and) " " (par v))]
        [(Or u v)    (~a (par u) " " (~sym 'or)  " " (par v))]
        [(Equal u v) (~a (par u) " " (~sym '=)   " " (par v))]
        ; powers
        [(Expt u 1/2) #:when (output-sqrt?) ((output-format-sqrt) u)]
        [(Expt u -1)    (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                        (format/ 1 (par u #:use quotient-sub))]
        ; unnormalized power of a power
        [(Expt (and (Expt u v) w) w1) (~a ((output-sub-exponent-wrapper) ; braces for tex otherwise nothing
                                           (v~ w)) 
                                          (~sym '^) ((output-sub-exponent-wrapper)
                                                     (fluid-let ([original? #t])
                                                       (par v #:use exponent-sub
                                                            #:wrap-fractions? #t))))]
        [(Expt u p)   (~a (par u #:use base-sub)
                          (~sym '^) ((output-sub-exponent-wrapper)
                                     ((output-format-function-symbol)
                                      (fluid-let ([original? #t])
                                         (par p #:use exponent-sub)))))]
        [(Expt u α)     #:when (= (numerator α) -1) ; -1/p
                        (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                        (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub))]
        [(Expt u v)   (~a (par u #:use base-sub)
                          (~sym '^) ((output-sub-exponent-wrapper)
                                     ((output-format-function-symbol)
                                      (fluid-let ([original? #t])
                                        (par v #:use exponent-sub #:wrap-fractions? #t)))))]
        [(Log u)      ((output-format-log) u)]
        [(Log u v)    ((output-format-log) u v)]
        [(Up u v)    ((output-format-up)  u v)]
        
        [(app: f us) #:when (memq f '(< > <= >=))
                     (match us [(list u v) (~a (v~ u) (~relop f) (v~ v))])]
        ; unnormalized quotient
        [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                       (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
        ; unormalized sqr
        [(list 'sqr u) (v~ `(expt ,u 2))]
        ; unormalized sqrt
        [(list 'sqrt u)   ((output-format-sqrt) u)]
        ; unnormalized root
        [(list 'root u v) ((output-format-root) u v)]
        ; unnormalized diff
        [(list 'diff (list 'sqrt u) x)
         #:when (member x (output-differentiation-mark))
         (~a "(" ((output-format-sqrt) u) ")'")]
        [(list 'diff f)
         #:when (symbol? f)                              (~a (~sym f) "'")]
        [(list 'diff (list f x) x)
         #:when (and (symbol? f) (symbol? x))            (~a (~sym f) "'(" (~var x) ")")]
        [(list 'diff u x)
         #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
        [(list 'diff u  x)                               (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]

        [(list 'percent u) (~a (v~ u) (~sym '|%|))]
        [(list 'abs u) ((output-format-abs) u)] 
        [(list 'vec u) (~a "\\overrightarrow{" (v~ u) "}")] ; TODO: only for TeX 
        [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
        [(list 'hat u) (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX 

        ; applications
        [(app: f us) (let ()
                       (define arguments
                         (apply string-append (add-between (map v~ us) ",")))
                       (define head ((output-format-function-symbol) f))
                       (~a head app-left arguments app-right))]
        [_  (wrap u)]))
    (define (t1~ u) ; term 1 aka first term in a sum
      (when debugging? (displayln (list 't1 u)))
      (math-match u
                  [(list 'red   u) (~red  (t1~ u))]
                  [(list 'blue  u) (~blue (t1~ u))]           ; blue color
                  [(list 'paren u ...) (~explicit-paren (map t1~ u))] ; explicit parens (tex)

                  ; unnormalized and normalized quotients
                  [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                                 (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
                  [(Quotient u v) #:when (and  (output-use-quotients?) (not (rational? v)))
                                  (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                                  (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
                  [(⊗  1 u)                       (~a                          (v~ u))]
                  [(⊗ -1 u)                       (prefix-minus (v~ u))]
                  ; integer
                  ; Explicit multiplication between integers
                  [(⊗  p q)                       (~a (~num p)  (~sym '*) (par q))]
                  ; [(⊗  p u) #:when (negative? p)  (~a (~sym '-) (~num (abs p)) (v~ u))] ; 
                  ; [(⊗  p u) #:when (positive? p)  (~a           (~num (abs p)) (v~ u))]
                  ; rationals (non-integer)
                  ; Explicit multiplication between rationals
                  [(⊗  α β)                       (~a (~num α) (~sym '*) (par β))]                  
                  ; problem: if u is a number we need an explicit *
                  ; [(⊗  α u) #:when (negative? α)  (~a (~sym '-) (~num (abs α)) (v~ u))] 
                  ; [(⊗  α u) #:when (positive? α)  (~a           (~num (abs α)) (v~ u))]
                  ; other reals
                  [(⊗  r s)                       (~a     (~num r) (~sym '*) (par s))]
                  ; explicit multiplication for powers with numbers as base
                  [(⊗ r (and (Expt (num: s) u) v)) #:when (negative? r) (~a "-" (~num (abs r)) (~sym '*) (v~ v))] ; XXX
                  [(⊗ r (and (Expt (num: s) u) v)) #:when (positive? r) (~a     (~num (abs r)) (~sym '*) (v~ v))]
                  
                  [(⊗  r u) #:when (negative? r)  (~a (~sym '-) (~num (abs r)) (implicit* r u) (par u))] ; XXX
                  [(⊗  r u) #:when (positive? r)  (~a           (~num (abs r)) (implicit* r u) (par u))] ; XXX
                  [u                                                           (v~ u) ]))
    (when debugging? (write (list 'v~ u 'orig original?)) (newline))
    (math-match u
      [(? string? u) u]
      [(list 'red   u) (~red  (v~ u))]
      [(list 'blue  u) (~blue (v~ u))]           ; blue color
      [(list 'paren u ...) (~explicit-paren (map v~ u))] ; explicit parens (tex)
      [(list 'formatting options u)
       (let loop ([os options])
         (match os
           ['()                                   (v~ u)]
           [(list (list 'use-quotients? v) os ...) (parameterize ([output-use-quotients? v]) (loop os))]
           [_                                     (error 'verbose-formatting (~a "unknown option" os))]))]
      [α           (~frac α)]
      [r           (~num r)]
      [r.bf        (bigfloat->string r.bf)]
      [x           (~a (~var x))]
      ; unnormalized and normalized quotients
      [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                     (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
      [(Quotient u v) #:when (and  (output-use-quotients?) (not (rational? v)))
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
      [(Expt u -1)    (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ 1 (par u #:use quotient-sub))]
      [(Expt u p)     #:when (negative? p)
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ 1 (par (Expt u (- p)) #:use quotient-sub #:exponent-base? #t))]
      [(Expt u α)     #:when (and (output-root?) (= (numerator α) 1) ((output-format-root) u (/ 1 α))) ; α=1/n
                      ((output-format-root) u (/ 1 α))] ; only used, if (output-format-root) returns non-#f 
      [(Expt u α)     #:when (= (numerator α) -1) ; -1/p
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub #:exponent-base? #t))]
      
      ; mult
      [(⊗  1 v)                                               (~a             (v~ v))]
      [(⊗ -1 α) #:when (negative? α)                          (~a "-" (paren  (v~ α)))]
      [(⊗ -1 x)                                               (~a "-"         (v~ x))]
      [(⊗ -1 v)                                               (~a "-" (paren  (v~ v)))]      
      [(⊗ -1 p v) #:when (and original? (negative? p))        ; (displayln (list "A" p v (⊗ p v)))
                                                              (~a "-" (paren  (v~ (⊗ p v) #f)))] ; wrong
      [(⊗ -1 v)   #:when      original?                       (~a "-"         (v~ v))]
      ; [(⊗ -1 p v) #:when                (negative? p)         (~a "-" (paren  (v~ (⊗ p v) #f)))]                 ; wrong
      [(⊗ -1 v)                                        (paren (~a "-"         (v~ v)))]
      ; Explicit multiplication between integers
      [(⊗ p q) #:when original?           (~a (~num p) (~sym '*) (par q))]
      [(⊗ p q) #:when (not (negative? p)) (~a (~num p) (~sym '*) (par q))]
      [(⊗ p q) #:when      (negative? p)  (~a "(" (~num p) ")" (~sym '*) (par q))]
      ; An implicit multiplication can not be used for fractions 
      ;[(⊗ p v)  #:when (negative? p)        (~a "-" (~num (abs p)) implicit-mult (par v #:use paren))]
      ;[(⊗ p v)  #:when (positive? p)        (~a     (~num (abs p)) implicit-mult (par v #:use paren))]
      ;[(⊗ α u)  #:when (= (numerator α)  1) (~a   "\\frac{" (v~ u) "}{"     (~num (/      α))  "}")]
      ;[(⊗ α u)  #:when (= (numerator α) -1) (~a   "\\frac{" (v~ u) "}{" "-" (~num (/ (abs α))) "}")]
      ; Implicit multiplication only if we have a symbols as base
      [(⊗ r (and (Expt (var: x) u) v)) #:when (negative? r) (if original?
                                                                (~a            "-" (~num (abs r))   implicit-mult (v~ v #t))
                                                                (~a (paren (~a "-" (~num (abs r)))) implicit-mult (v~ v #t)))] ; XXXXX *
      [(⊗ r (and (Expt (var: x) u) v)) #:when (positive? r) (~a                    (~num (abs r))   implicit-mult (v~ v #t))]
      ; Implicit multiplication between numbers and variables
      [(⊗ r x)  (~a (~num r) (~var x))] ; XXXX

      ; Use explicit multiplication for fractions
      [(⊗ r (⊗ u v))  #:when (and (negative? r) (not (equal? '(*) v))) 
                      (~a "-" (~num (abs r)) (implicit* r u) (v~ (argcons '* u v)))]
      [(⊗ r (⊗ u v))  #:when (and (positive? r) (not (equal? '(*) v))) 
                      (~a    (~num (abs r))  (implicit* r u) (v~ (argcons '* u v)))] ; XXX
      [(⊗ r v)        #:when (negative? r) 
                      (define w (if original? values paren))
                      (~a  (w (~a "-" (~num (abs r)))) (implicit* r v) (par v #:use paren))] ; XXX
      [(⊗ r v)        #:when (positive? r) 
                      (~a     (~num r) (implicit* r v) (par v #:use paren))] ; XXX
      
      [(⊗ u v)  #:when (not (equal? '(*) v))    (~a (par u) (implicit* u v)  (par v))]
      ; plus
      [(⊕ u r)              (if (negative? r)
                                (~a (t1~ u)  (~sym '-) (~num (abs r)))
                                (~a (t1~ u)  (~sym '+) (~num (abs r))))]
      [(⊕ u (⊗ -1 v))       (~a (t1~ u)  (~sym '-) (v~ v))]
      ; Unnormalized (in a normalized expression only the first factor can be a number)
      [(⊕ u (⊗  r s))        #:when (negative? r) (~a (t1~ u)  (~sym '-) (~num (abs r)) (~sym '*) (par s))]
      [(⊕ u (⊗  r s))        #:when (positive? r) (~a (t1~ u)  (~sym '+) (~num (abs r)) (~sym '*) (par s))]
      ; previous two rules ensure that v is non-empty
      [(⊕ u (⊗  r (⊗ s v)))  #:when (negative? r) 
                            (~a (t1~ u)  (~sym '-) (~num (abs r)) (~sym '*) (par s) (~sym '*) (v~ v))]
      [(⊕ u (⊗  r (⊗ s v)))  #:when (positive? r) 
                             (~a (t1~ u) (~sym '+) (~num (abs r)) (~sym '*) (par s) (~sym '*) (v~ v))]
      ;
      [(⊕ u (⊗  r v))       #:when (negative? r)
                            (~a (t1~ u)  (~sym '-) (v~ (⊗ (abs r) v)))]
      [(⊕ u (⊗  r v))       #:when (positive? r) 
                            (~a (t1~ u)  (~sym '+) (v~ (⊗ r v)))]
      [(⊕ u (⊕ (⊗ -1 v) w)) (~a (t1~ u)  (~sym '-) (v~ (argcons '+ v w)))]
;      [(⊕ u (⊕ (⊗  r v) w)) #:when (negative? r) (displayln (list 'EEE r v))
;                            (~a (t1~ u)  (~sym '-) (v~ (argcons '+ (list '* (abs r) v) w)))]
;      [(⊕ u (⊕ (⊗  r v) w)) #:when (positive? r) (displayln (list 'FFF r v))
;                            (~a (t1~ u)  (~sym '+) (v~ (argcons '+ (list '* (abs r) v) w)))]

      ; TODO: Problem: If v is a negative number, we need a paren around v.
      ;; [(⊕ u (⊕ (⊗  r v) w)) #:when (negative? r) (displayln (list 'EEE r v))
      ;;                       (~a (t1~ u)  (~sym '-) (~num (abs r)) (implicit* r v) (v~ (argcons '+ v w)))]
      ;; ; TODO: Problem: If v is a negative number, we need a paren around v.
      ;; [(⊕ u (⊕ (⊗  r v) w)) #:when (positive? r)  (displayln (list 'FFF r v))
      ;;                       (~a (t1~ u)  (~sym '+) (~num (abs r)) (implicit* r v) (v~ (argcons '+ v w)))]
      [(⊕ u v)              (match v
                              [(? number? r)               #:when (negative? r)  (~a (t1~ u) (v~ v))]
                              [(list* '* (? number? r) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
                              [(list* '+ (? number? r) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
                              [(list* '+ (list* '* (? number? r) _) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
                              [_                                                 (~a (t1~ u)  (~sym '+) (v~ v))])]
      ; minus (doesn't appear in normalized expressions)
      [(list  '- u)          (~a (~sym '-) (par u #:use paren))]
      [(list* '- u v)        (~a (t1~ u) (~sym '-)
                                 (par (match v
                                        [(list v)   v]
                                        [(list* vs) (cons '+ vs)])
                                      #:use paren))]
      ; other
      [(And (Less u v) (Less u1 v1))           #:when (equal? v u1)
       (~a (par u) " " (~sym '<) " " (par v) " " (~relop '<) " " (par v1))]
      [(And (LessEqual u v) (Less u1 v1))      #:when (equal? v u1)
       (~a (par u) " " (~sym '<=) " " (par v) " " (~relop '<) " " (par v1))]
      [(And (LessEqual u v) (LessEqual u1 v1)) #:when (equal? v u1)
       (~a (par u) " " (~sym '<=) " " (par v) " " (~relop '<=) " " (par v1))]
      [(And (Less u v)      (LessEqual u1 v1)) #:when (equal? v u1)
       (~a (par u) " " (~sym '<)  " " (par v) " " (~relop '<=) " " (par v1))]
      
      [(And u v)            (~a (par u) " " (~sym 'and) " " (par v))]
      ; todo: if u or v contains And or Or in u or v then we need parentheses as in the And line
      [(Or u v)             (~a (v~ u) " " (~sym 'or) " " (v~ v))]      
      [(list  '= v) (~a (~sym '=) (v~ v))]
      [(list* '= us) ; handle illegal = with multiple terms
       (string-append* (add-between (map (λ (u) (v~ u #t)) us) (~a " " (~relop '=) " ")))]
      [(list  '~ v)      (~a (~sym '~) (v~ v))]
      [(list* '~ us)
       (string-append* (add-between (map (λ (u) (v~ u #t)) us) (~a " " (~relop '~) " ")))]
      [(Equal u v)        (~a (v~ u #t)  " " (~relop '=) " " (v~ v #t))] ; never reached!!
      ; [(⊖ u v)     (~a (par u) "-" (v~ v))]
      ; [(⊘ u v)     (~a (par u) (~sym '/) (par v))]      
      [(Expt u 1/2) #:when (output-sqrt?) ((output-format-sqrt) u)]
      ; unnormalized power of a power
      [(Expt (and (Expt u v) w) w1)   (~a ((output-sub-exponent-wrapper)
                                          (v~ w)) 
                                         (~sym '^) (fluid-let ([original? #t])
                                                     ((output-sub-exponent-wrapper)
                                                      (par w1 #:use exponent-sub
                                                           #:wrap-fractions? #t))))]
      [(Expt u v)  (~a (par u #:exponent-base? #t) (~sym '^) (fluid-let ([original? #t])
                                           ((output-sub-exponent-wrapper)
                                            (par v #:use exponent-sub
                                                 #:wrap-fractions? #t))))]
      ; Unnormalized
      [(list 'sqr u) (v~ `(expt ,u 2))]
      
      ;   handle sqrt first
      [(list 'diff (list 'sqrt u) x)
       #:when (member x (output-differentiation-mark))
       (~a "(" ((output-format-sqrt) u) ")'")]      
      [(list 'diff f)
       #:when (symbol? f)                     (~a (~sym f) "'")]
      [(list 'diff (list f x) x)
       #:when (and (symbol? f) (symbol? x))   (~a (~sym f) "'(" (~var x) ")")]
      [(list 'diff u x)
       #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
      [(list 'diff u  x)                      (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]
      
      [(Equal u v) (~a (v~ u #t) (~sym '=) (v~ v #t))]
      [(Log u)     ((output-format-log) u)]
      [(Log u v)   ((output-format-log) u v)]
      [(Up u v)    ((output-format-up)  u v)]
      [(Piecewise us vs)    (string-append*
                             (append (list "\\begin{cases}\n")
                                     (for/list ([u us] [v vs])
                                       (~a (v~ u) " & " (v~ v) "\\\\\n"))
                                     (list "\\end{cases}")))]
      [(list 'sqrt u)   ((output-format-sqrt) u)]   ; unnormalized sqrt
      [(list 'root u v) ((output-format-root) u v)] ; unnormalized root
      [(list 'percent u) (~a (v~ u) (~sym '|%|))]

      [(list 'abs u) ((output-format-abs) u)] 
      [(list 'vec u) (~a "\\overrightarrow{" (v~ u) "}")] ; TODO: only for TeX 
      [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
      [(list 'hat u) (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX 

      [(app: f us) #:when (memq f '(< > <= >=))
                   (match us [(list u v) (~a (v~ u) (~sym f) (v~ v))])]
      [(app: f us) (let ()
                     (define arguments
                       (apply string-append (add-between (map v~ us) ",")))
                     (define head ((output-format-function-symbol) f))
                     (~a head app-left arguments app-right))]
      [_ (display u)
         (error 'verbose~ (~a "internal error, got: " u))]))

  ((output-wrapper) (v~ u #t)))

(define (reverse-plus u)
  (define r reverse-plus)
  (match u
    [(list* '+ us) (list* '+ (reverse us))]
    [(list* op us) (list* op (map r us))]
    [u             u]))

(define (~ u)
  (match (output-terms-descending?)
    [#t (verbose~ (reverse-plus u))]
    [#f (verbose~ u)]))

(module+ test
  (check-equal? (verbose~ '(- (- x 3))) "-(x-3)")
  (parameterize ([output-implicit-product? #t])
    (check-equal? (verbose~ (expand (Expt (⊕ x 1) 3))) "1+3x+3x^2+x^3"))
  (check-equal? (verbose~ (Sin (⊕ x -7))) "sin(-7+x)")
  (check-equal?
   (verbose~ (normalize '(* (sin (+ x -7)) (+ (cos (+ x -7)) (asin (+ x -7))))))
   "sin(-7+x)*(asin(-7+x)+cos(-7+x))")
  (check-equal? (parameterize ([bf-precision 100]) (verbose~ pi.bf))
                "3.1415926535897932384626433832793")
  ; --- MMA
  (use-mma-output-style)
  (check-equal? (~ (Sin (⊕ x -7))) "Sin[-7+x]")
  (use-default-output-style)
  (check-equal? (~ (Sin (⊕ x -7))) "sin(-7+x)")
  (check-equal? (~ '(* -1 x)) "-x")
  (check-equal? (~ '(+ (* -1 x) 3)) "-x+3")
  (check-equal? (~ '(+ (expt x 2) (* -1 x) 3)) "x^2-x+3")
  (check-equal? (~ (normalize '(/ x (- 1 (expt y 2))))) "x/(1-y^2)")
  (check-equal? (~ '(* 2 x y)) "2*x*y")
  ; —–- TeX
  (use-tex-output-style)
  (check-equal? (~ 4)   "$4$")
  (check-equal? (~ 2/3) "$\\frac{2}{3}$")
  (check-equal? (~ (normalize '(/ x (- 1 (expt y 2))))) "$\\frac{x}{1-y^{2}}$")
  (check-equal? (~ '(* -8 x )) "$-8x$")
  (check-equal? (~ '(- 1 (+ 2 3))) "$1-(2+3)$")
  (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "$4(-7-a)$")
  (check-equal? (~ '(* 3 6)) "$3\\cdot 6$")
  (check-equal? (~ '(sqrt d)) "$\\sqrt{d}$")
  (check-equal? (~ '(* (sqrt d) a)) "$\\sqrt{d}\\cdot a$")
  (check-equal? (~ '(* -4 (expt -1 3))) "$-4\\cdot {(-1)}^{3}$")
  (check-equal? (~ '(* -9 (expt x -10))) "$\\frac{-9}{x^{10}}$")
  (check-equal? (~ '(- (* 2 3) (* -1  4))) "$2\\cdot 3-(-4)$")
  (check-equal? (~ '(- (* 2 3) (* -1 -4))) "$2\\cdot 3-(-(-4))$")
  (check-equal? (~ '(paren -3)) "${\\left(-3\\right)}$")
  (check-equal? (~ '(red  (paren -3))) "${\\color{red}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(blue (paren -3))) "${\\color{blue}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(paren x_1 y_1))   "${\\left(x_1,y_1\\right)}$")
  (check-equal? (~ '(~ X (bi n p)))    "$X \\sim  bi(n,p)$")
  (check-equal? (~ '(* 1/2 1/3))               "$\\frac{1}{2}\\cdot \\frac{1}{3}$")
  (check-equal? (~ '(sqrt (* 1/2 1/3))) "$\\sqrt{\\frac{1}{2}\\cdot \\frac{1}{3}}$")
  (check-equal? (~ '(sqrt (* 12 1/12 11/12))) "$\\sqrt{12\\cdot \\frac{1}{12}\\cdot \\frac{11}{12}}$")
  (parameterize ([output-root? #t]) (check-equal? (~ '(expt 2 1/3)) "$\\sqrt[3]{2}$"))
  (check-equal? (tex '(- (sqr c) (sqr a))) "$c^{2}-a^{2}$")
  ; --- Default
  (use-default-output-style)
  (check-equal? (~ '(* -1 x)) "-x")
  (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "4*(-7-a)")
  (check-equal? (~ '(+ (* -3 (- x -2)) -4)) "-3*(x-(-2))-4")
  (check-equal? (~ '(+ (*  3 (- x -2)) -4)) "3*(x-(-2))-4")
  (check-equal? (~ '(+ (*  3 (- x 2)) -4)) "3*(x-2)-4")
  (check-equal? (~ `(+ (expt 2 3) (* 5 2) -3)) "2^3+5*2-3")
  (check-equal? (~ '(+ (expt -1 2) (* 3 -1) -2)) "(-1)^2+3*(-1)-2")
  (check-equal? (~ '(+ 1 -2 3)) "1-2+3")
  (check-equal? (~ '(+ 1 (* -2 x) 3)) "1-2*x+3")
  (check-equal? (parameterize ([output-sqrt? #f]) (~ '(expt x 1/2))) "x^(1/2)")
  (check-equal? (parameterize ([output-sqrt? #t]) (~ '(expt x 1/2))) "sqrt(x)")
  (check-equal? (~ '(+ 1 (* 7 (expt x -1)))) "1+7/x")
  (check-equal? (~ '(formatting ([use-quotients? #f]) (+ 1 (* 7 (expt x -1))))) "1+7*1/x")
  (check-equal? (~ '(formatting ([use-quotients? #t]) (+ 1 (* 7 (expt x -1))))) "1+7/x")
  (check-equal? (~ '(expt (expt 65 1/2) 2)) "sqrt(65)^2")
  )

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

;(require latex-pict pict)
;(define (render u)
;  (define (strip$ x) (substring x 1 (- (string-length x) 1)))
;  (pict->bitmap (scale (tex-math (strip$ (tex u))) 2)))


;;; Example from the REPL.

; Require start makes ' automatically normalize all expressions.

; (displayln "Enter the following in the REPL to redefine ' to do automatic simplification.")
; (write '(require (submod "." start))) (newline)
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
;> (render '(+ x 1))
; ...

;; ;;;
;; ;;; FORMATTING
;; ;;;

;; ;;; Variables and Constants

;; ; The parameter output-variable-name holds the formatter
;; ; for variables and constants.

;; ; Input  Default   TeX           MMA
;; ; @e     e         \mathrm{e}    E
;; ; @pi    pi        π             Pi
;; ; @i     i         i             i
;; ; x      x         x             x

;; ; TeX handles various other symbols in symbol->tex.

;; (define (default-output-variable-name x)
;;   (match x ['@pi "pi"] ['@e "e"] ['@i "i"]           [_ (~a x)]))
;; (define (mma-output-variable-name x)
;;   (match x ['@pi "Pi"] ['@e "E"] ['@i "i"]           [_ (~a x)]))
;; (define (tex-output-variable-name x)
;;   (match x ['@pi "π"]  ['@e "\\mathrm{e}"] [_ (symbol->tex x)]))

;; ;;; Fractions

;; (define (default-output-fraction α) (~a α))
;; (define (mma-output-fraction     α) (~a α))
;; (define (tex-output-fraction     α) 
;;   (if (> (%denominator α) 1)
;;       (~a "\\frac{" (%numerator α) "}{" (%denominator α) "}")
;;       (~a α)))

;; ;;; Roots

;; ; If output-root? is true, the formatter uses output-root to output
;; ; powers of the form (expt u 1/n).

;; (define (default-output-root u n)
;;   ; note: KAS can't parse root(u,n) so we need to output u^(1/n)
;;   #f) ; this makes verbose! output u^(1/n) with correct parens

;; ;; (define (mma-output-root formattted-u) 
;; ;;   (match u
;; ;;     [(Expt u α) #:when (= (numerator? α) 1) (def n (/ 1 α)) (~a "Power[" formattted-u "," α ")")]
;; ;;     [_ (error 'mma-output-root (~a "Expected expression of the form (expt u 1/n), got: " u))]))

;; ;; (define (tex-output-root formattted-u) 
;; ;;   (match u
;; ;;     [(Expt u α) #:when (= (numerator? α) 1)  (def n (/ 1 α)) (~a "\\sqrt[" n " ]{" formatted-u "}")]
;; ;;     [_ (error 'tex-output-root (~a "Expected expression of the form (expt u 1/n), got: " u))]))


;; ;;; Logarithms

;; ; Input      Default    Tex          MMA
;; ; (log x)    log(x)     \log(x)      log(x)
;; ; (log 2 x)  log_2(x)   \log_{2}(x)  log_2(x) 

;; (define (default-output-log u [v #f])
;;   (match-define (list l r) (output-application-brackets))
;;   (cond [v    (~a "log_" (verbose~ u) l (verbose~ v) r)]
;;         [else (~a "log" l (verbose~ u) r)]))

;; (define (default-output-up u v)
;;   (~a "(" (verbose~ u) "," (verbose~ v) ")"))


;; (define mma-output-log default-output-log)

;; (define (tex-output-log u [v #f])
;;   (parameterize ([output-wrapper values])
;;     (cond [v    (~a "\\log_{" (verbose~ u) "}(" (verbose~ v) ")")]
;;           [else (~a "\\log(" (verbose~ u) ")")])))

;; (define (tex-output-up u v)
;;   (parameterize ([output-wrapper values])
;;     (define x (verbose~ u))
;;     (define y (verbose~ v))
;;     (~a "\\begin{pmatrix} " x "\\\\" y "\\end{pmatrix}")))

;; ;;; Formatting Parameters

;; (define output-application-brackets      (make-parameter (list "(" ")")))
;; (define output-format-function-symbol    (make-parameter ~a))
;; (define output-format-quotient           (make-parameter #f)) ; #f means default u/v
;; (define output-format-quotient-parens    (make-parameter (list "(" ")"))) 
;; (define output-sub-expression-parens     (make-parameter (list "(" ")")))
;; (define output-wrapper                   (make-parameter values))
;; (define output-use-quotients?            (make-parameter #t))
;; (define output-sqrt?                     (make-parameter #t)) ; use sqrt to output (expt u 1/2) ; otherwise as expt
;; (define output-root?                     (make-parameter #t)) ; use root to output (expt u 1/n) ; otherwise as expt
;; (define output-format-abs                (make-parameter (λ(u)   (~a "abs("  (verbose~ u) ")"))))
;; (define output-format-sqrt               (make-parameter (λ(u)   (~a "sqrt(" (verbose~ u) ")"))))
;; (define output-format-root               (make-parameter default-output-root))
;; (define output-format-log                (make-parameter default-output-log))
;; (define output-format-up                 (make-parameter default-output-up))
;; (define output-sub-exponent-parens       (make-parameter (list "(" ")"))) ; for Tex it is { }
;; (define output-sub-exponent-wrapper      (make-parameter values))         ; TeX needs extra {}
;; (define output-terms-descending?         (make-parameter #f)) ; reverse terms before outputting?
;; (define output-implicit-product?         (make-parameter #f)) ; useful for TeX
;; (define output-relational-operator       (make-parameter ~a)) ; useful for TeX
;; (define output-floating-point-precision  (make-parameter 4))  ; 
;; (define output-variable-name             (make-parameter default-output-variable-name)) ; also handles @e, @pi, and @i
;; (define output-differentiation-mark      (make-parameter '(x))) ; use (u)' rather than d/dx(u) for variables in this list
;; (define output-fraction                  (make-parameter default-output-fraction))

;; (define (use-mma-output-style)
;;   (output-application-brackets (list "[" "]"))
;;   (output-format-function-symbol (λ(s) (string-titlecase (~a s))))
;;   (output-format-quotient #f)
;;   (output-format-quotient-parens (list "(" ")"))
;;   (output-sub-expression-parens  (list "(" ")"))
;;   (output-wrapper values)
;;   (output-sqrt? #t)
;;   (output-format-abs  (λ(u)   (~a "Abs["  (verbose~ u) "]")))
;;   (output-format-sqrt (λ(u)   (~a "Sqrt[" (verbose~ u) "]")))
;;   (output-format-root (λ(u n) (~a "Root[" (verbose~ u) "," (verbose~ n) "]")))
;;   (output-format-log mma-output-log)
;;   (output-format-up           default-output-up)
;;   (output-sub-exponent-parens (list "(" ")"))
;;   (output-sub-exponent-wrapper values)
;;   (output-implicit-product? #f)
;;   (output-relational-operator ~a)
;;   (output-variable-name mma-output-variable-name)
;;   (output-fraction mma-output-fraction))

;; (define (use-default-output-style)
;;   (output-application-brackets (list "(" ")"))
;;   (output-format-function-symbol ~a)
;;   (output-format-quotient #f)
;;   (output-format-quotient-parens (list "(" ")"))
;;   (output-sub-expression-parens  (list "(" ")"))
;;   (output-sub-exponent-parens    (list "(" ")"))
;;   (output-sub-exponent-wrapper   values)
;;   (output-wrapper values)
;;   (output-sqrt? #t)
;;   (output-root? #f)
;;   (output-format-abs  (λ(u)   (~a "abs("  (verbose~ u) ")")))
;;   (output-format-sqrt (λ(u)   (~a "sqrt(" (verbose~ u) ")")))
;;   (output-format-root (λ(u n) (~a "root(" (verbose~ u) "," (verbose~ n) ")")))
;;   (output-format-log default-output-log)
;;   (output-format-up  default-output-up)
;;   (output-implicit-product? #f)
;;   (output-relational-operator ~a)
;;   (output-variable-name default-output-variable-name)
;;   (output-fraction default-output-fraction))

;; (define (use-tex-output-style)
;;   (define operators '(sin cos tan log ln sqrt det))
;;   (define (~relop u)
;;     (match u
;;       ['<=  "≤ "]
;;       ['>=  "≥ "]
;;       [_    (~a u)]))
;;   (define (~symbol s) 
;;     (match s
;;       ['acos "\\cos^{-1}"]
;;       ['asin "\\sin^{-1}"]
;;       ['atan "\\tan^{-1}"]
;;       [_ #:when (member s operators) (~a "\\" s)]
;;       ['<=  "\\leq "]
;;       ['>=  "\\geq "]
;;       ['*   "\\cdot "]
;;       ['or  "\\vee "]
;;       ['and "\\wedge "]
;;       [_  (~a s)]))
;;   (output-application-brackets (list "(" ")"))
;;   (output-format-function-symbol ~symbol)
;;   (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
;;   (output-format-quotient-parens (list "" "")) ; not needed due to {} from \frac
;;   ; (output-use-quotients? #t)
;;   (output-sub-expression-parens (list "{" "}"))
;;   (output-wrapper (λ (s) (~a "$" s "$")))
;;   (output-format-abs  (λ(u)   (parameterize ([output-wrapper values])
;;                                 (~a "\\left|"  (verbose~ u) "\\right|"))))  
;;   (output-sqrt? #t)
;;   (output-root? #f)
;;   (output-format-sqrt (λ(u)   (parameterize ([output-wrapper values])
;;                                 (~a "\\sqrt{"  (verbose~ u) "}"))))  
;;   (output-format-root (λ(u n) (parameterize ([output-wrapper values])
;;                                 (if (equal? n 2)
;;                                     (~a "\\sqrt{" (verbose~ u) "}")
;;                                     (~a "\\sqrt[" (verbose~ n) "]{" (verbose~ u) "}")))))
;;   (output-format-log tex-output-log)
;;   (output-format-up  tex-output-up)
;;   (output-sub-exponent-parens  (list "{" "}"))
;;   (output-sub-exponent-wrapper (λ (s) (~a "{" s "}")))
;;   (output-implicit-product? #t)
;;   (output-relational-operator ~relop)
;;   (output-variable-name tex-output-variable-name)
;;   (output-fraction tex-output-fraction))

;; (define (tex u)
;;   (define operators '(sin  cos  tan log ln sqrt
;;                            det
;;                       sinh cosh tanh )) ; needs \\ in output
;;   (define relational-operators '(= < <= > >=))
;;   (define (~relop u)
;;     (match u
;;       ['<=  "≤ "]
;;       ['>=  "≥ "]
;;       [_    (~a u)]))
;;   (define (~symbol s)
;;     (match s
;;       ['acos "\\cos^{-1}"]
;;       ['asin "\\sin^{-1}"]
;;       ['atan "\\tan^{-1}"]
;;       [_ #:when (member s operators) (~a "\\" s)]      
;;       ['<=  "\\leq "]
;;       ['>=  "\\geq "]
;;       ['*   "\\cdot "]   ; multiplication
;;       ['or  "\\vee "]    ; logical or
;;       ['and "\\wedge "]  ; logical and
;;       ['|%| "\\%"]
;;       [_  (~a s)]))
;;   (parameterize ((output-application-brackets (list "(" ")"))
;;                  (output-format-function-symbol ~symbol)
;;                  (output-format-quotient (λ (u v) (~a "\\frac{" u "}{" v "}")))
;;                  (output-format-quotient-parens (list "" ""))
;;                  ; (output-use-quotients? #t)
;;                  (output-sub-expression-parens (list "{" "}"))
;;                  (output-wrapper (λ (s) (~a "$" s "$")))
;;                  ; (output-sqrt? #t) ; uncommented!! otherwise the user can't control it
;;                  (output-format-sqrt (λ(u) (parameterize ([output-wrapper values])
;;                                              (~a "\\sqrt{" (verbose~ u) "}"))))
;;                  (output-format-root (λ(u n) (parameterize ([output-wrapper values])
;;                                                (if (equal? n 2)
;;                                                    (~a "\\sqrt{" (verbose~ u) "}")
;;                                                    (~a "\\sqrt[" (verbose~ n) "]{" (verbose~ u) "}")))))
;;                  (output-sub-exponent-parens  (list "{" "}"))
;;                  (output-sub-exponent-wrapper (λ (s) (~a "{" s "}")))
;;                  (output-implicit-product?    #t)
;;                  (output-relational-operator  ~relop)
;;                  (output-variable-name        tex-output-variable-name)
;;                  (output-format-log           tex-output-log)
;;                  (output-format-up            tex-output-up)
;;                  (output-fraction             tex-output-fraction))
;;     (verbose~ u)))

;; (define char->tex
;;   (let ()
;;     (define dict
;;       ( hash
;;        ; symbolic constants
;;        'α "\\alpha"   'β "\\beta"    'γ "\\gamma"   'Γ "\\Gamma" 'δ "\\delta" 'Δ "\\Delta"
;;        'ε "\\epsilon" 'ζ "\\zeta"    'η "\\eta"     'θ "\\theta" 'Θ "\\Theta" 'ι "\\iota"
;;        'κ "\\kappa"   'λ "\\lambda"  'Λ "\\Lambda"  'μ "\\mu"    'ν "\\nu"    'ξ "\\xi"
;;        'Ξ "\\Xi"      'π "\\pi"      'Π "\\Pi"      'ρ "\\rho"   'σ "\\sigma" 'Σ "\\Sigma"
;;        'τ "\\Tau"     'υ "\\upsilon" 'Υ "\\Upsilon" 'φ "\\phi"   'Φ "\\Phi"   'χ "\\chi"
;;        'ψ "\\psi"     'Ψ "\\Psi"     'ω "\\omega"   'Ω "\\Omega" 
;;        '|%| "\\%"))
;;     (λ (c)
;;       (define s (string->symbol (string c)))
;;       (match (hash-ref dict s #f)
;;         [#f (string c)]
;;         [s  (~a s " ")]))))

;; (define (string->tex s)
;;   (define s1 (string-append* (map char->tex (string->list s))))
;;   (if (equal? s s1) s s1))

;; (define (symbol->tex s)
;;   (define t (string->symbol (string->tex (symbol->string s))))
;;   (match t
;;     ['@e  "\\mathrm{e}"]         ; Euler's constant
;;     ['@pi "\\pi"]      ; pi
;;     ['@i "i"]          ; the unit imaginary number
;;     ['@n  "@n"]        ; an arbitrary natural number
;;     ['@p  "@p"]        ; an arbitrary integer
;;     ['|%|  "\\%"]        ; an arbitrary integer
    
;;     [_ t]))


;; (define (prepare-unnormalized-for-formatting
;;          u
;;          #:zero-term   [zero-term   #f]  ; remove  0 in sums
;;          #:one-factor  [one-factor  #f]  ; rewrite (* 1 u) to u
;;          #:zero-factor [zero-factor #f]  ; rewrite (* 0 u) to 0
;;          #:all         [all         #t])
;;   ; the purpose of this function is to reuse the formatter for normalized
;;   ; expressions, for formatting unnormalized expressions.
;;   (when all
;;     (set! zero-term   #t)
;;     (set! one-factor  #t)
;;     (set! zero-factor #t))


;;   ;; Note: Differences and quotients does not appear in normalized expressions.
;;   ;;       Therefore we need to handle these with care.

;;   ;; The pattern ⊖ matches various differences
;;   ;;  (⊖ x y) matches (- a b)       and binds x->a, y->b
;;   ;;  (⊖ x y) matches (- a b c ...) and binds x->a, y->(+ b c ...)
;;   (define-match-expander ⊖
;;     (λ (stx)
;;       (syntax-parse stx
;;         [(_ u v) #'(or (list '- u v)
;;                        (list-rest '- u (app (λ(ys) (cons '+ ys)) v)))]
;;         [(_ u)       #'(list '- u)])))

;;   ;; The pattern ⊘ matches quotient
;;   ;;  (⊘ x y) matches (/ a b)       and binds x->a, y->b
;;   (define-match-expander ⊘
;;     (λ (stx)
;;       (syntax-parse stx
;;         [(_ u v) #'(list '/ u v)])))


;;   (define (argcons op u v)
;;     (match v
;;       [(list* (== op) vs) (list* op u vs)]
;;       [v                  (list  op u v)]))
  
;;   (define (p u)
;;     ; (displayln (list 'p u))
;;     (define (non-zero? u) (not (equal? 0 u)))
;;     (math-match u
;;      ; keep formatting declaration unchanged           
;;      [(list 'formatting options u)  `(formatting ,options ,(p u))]
;;      ; rewrites
;;      [(⊗ 1 v)         #:when one-factor (p v)]
;;      [(⊘ u 1)         #:when one-factor (p u)]
;;      [(⊗ 0 v)         #:when zero-factor 0]
;;      [(⊗ v 0)         #:when zero-factor 0]
;;      [(⊕ 0 v)         #:when zero-term  (p v)]
;;      [(⊕ v 0)         #:when zero-term  (p v)]
;;      [(⊕ (⊗ 0 u) v)   #:when zero-term  (p v)]
;;      [(⊕ (⊗ u 0) v)   #:when zero-term  (p v)]
;;      ; note: the above special cases a 0 as the second factor
;;      ;       a zero as third fact results in a zero term
;;      [(⊖ u 0)         #:when zero-term  (p u)]
;;      ; no rewrites
;;      [r               u]
;;      [r.bf            u]
;;      [x               u]
;;      ; rewrite sub expressions
;;      [(⊖ u)           (list     '- (p u)      )]
;;      [(⊖ u v)         (argcons  '- (p u) (p v))] 
;;      [(⊘ u v)         (list     '/ (p u) (p v))]  ; binary only     
;;      [(⊗ u v)         (argcons  '* (p u) (p v))]
;;      [(⊕ u v)         (match (list (p u) (p v))
;;                         [(list 0 0) 0]
;;                         [(list 0 u) u]
;;                         [(list u 0) u]
;;                         [(list u v) (argcons  '+ u v)])]
;;      [(⊕ u)           (p u)]
     
;;      ; other
;;      [(And   u v)     (argcons 'and (p u) (p v))]
;;      [(Or    u v)     (argcons 'or  (p u) (p v))]
;;      [(Equal u v)     (list    '=    (p u) (p v))]
;;      [(Expt  u v)     (list    'expt (p u) (p v))]
;;      [(Log   u)       (list    'log  (p u))]
;;      [(Log   u v)     (list    'log  (p u) (p v))]
;;      [(Piecewise us vs) (Piecewise: (map p us) (map p vs))]
;;      [(app: f us)     (cons f (map p us))]
;;      [_ (display u)
;;         (error 'prepare-unnormalized-for-formatting
;;                (~a "internal error, got: " u))]))
;;   (if (string? u)
;;       u
;;       (p u)))

;; (define prepare prepare-unnormalized-for-formatting)

;; ; ~ converts an expression into a string
;; ;  Originally it only formatted normalized expressions, but
;; ;  now unnormalized expressions are supported too.
;; ;  The output format is configured using parameters.
;; ;  The three builtin styles are default, mma and tex.
;; (define (verbose~ u)
;;   (when debugging? (displayln (list 'verbose~ u)))
;;   (match-define (list app-left  app-right)  (output-application-brackets))
;;   (match-define (list sub-left  sub-right)  (output-sub-expression-parens))
;;   (match-define (list expt-left expt-right) (output-sub-exponent-parens))
;;   (match-define (list quot-left quot-right) (output-format-quotient-parens))
;;   ;(define use-quotients? (output-use-quotients?))
;;   (define ~sym (let ([sym (output-format-function-symbol)]) (λ (x) (sym x)))) ; function names
;;   (define ~var (let ([out (output-variable-name)]) (λ(x) (out x)))) ; variable names
;;   (define (~relop x) ((output-relational-operator) x))
;;   (define (~red str)  (~a "{\\color{red}" str "\\color{black}}"))
;;   (define (~blue str) (~a "{\\color{blue}" str "\\color{black}}"))
;;   (define (~explicit-paren strs) (~a "{\\left(" (string-append* (add-between strs ",")) "\\right)}"))

;;   (define (v~ u [original? #f])
;;     (when debugging? (displayln (list 'v~ u 'orig original?)))
;;     (define ~frac (output-fraction))
;;     (define (~num r)
;;       (define precision (output-floating-point-precision))
;;       (cond [(and (exact? r) (> (%denominator r) 1)) (~frac r) (~a r)]
;;             [(exact? r) (~a r)]
;;             [(nan? r)   (~a r)]
;;             [precision  (~r r #:precision precision)]
;;             [else       (~a r)]))
;;     (define (paren u) ; always wrap in ( )
;;       (when debugging? (displayln (list 'paren u )))
;;       (~a "(" (v~ u #t) ")"))
;;     (define (exponent-wrap s)
;;       (~a expt-left s expt-right))
;;     (define (sub u) ; always wrap in sub-left and sub-right parentheses
;;       (~a sub-left (v~ u #t) sub-right))    
;;     (define (exponent-sub u) ; wraps the exponent of an expt-expression
;;       (exponent-wrap (v~ u #t)))
;;     (define (base-sub u) ; wraps the base of an expt-expression
;;       (if (and (number? u) (negative? u))
;;           ; we only need to add real parens, if expt-left aren't (
;;           (if (equal? expt-left "(")
;;               (~a expt-left (v~ u) expt-right)
;;               (~a expt-left (paren u) expt-right))
;;           (if (equal? expt-left "(")
;;               (~a expt-left (v~ u) expt-right)
;;               (~a expt-left (paren u) expt-right))))
;;     (define (quotient-sub u) ; wraps numerator or denominator of quotient
;;       (~a quot-left (v~ u) quot-right))
;;     (define implicit-mult (if (output-implicit-product?) "" (~sym '*)))
;;     (define (argcons op x xs)
;;       (match xs
;;         [(list* (== op) args) (list* op x args)]
;;         [args                 (list* op x (list args))]))
;;     (define (implicit* u v) ; returns either (~sym '*) or implicit-mult
;;       (when debugging? (displayln (list 'implicit* u v)))
;;       (math-match u
;;         [r (math-match v
;;              [s                    (~sym '*)]
;;              [x                     implicit-mult]
;;              [(⊗ u1 u2)            (implicit* r u1)]
;;              [(Expt u1 u2)         (implicit* r u1)]
;;              [(list '+ u1 u2 ...)   implicit-mult]
;;              [(list 'vec u1 u2 ...) implicit-mult]  
;;              [_                    (~sym '*)])]
;;         [_ (math-match v
;;              [@pi                   implicit-mult]
;;              [@e                    implicit-mult]
;;              [@i                    implicit-mult]
;;              [x                     implicit-mult]
;;              [(⊗ v1 v2)            (implicit* u v1)]
;;              [_                    (~sym '*)])]
;;         ))

;;     (define (prefix-minus s)
;;       (if (eqv? (string-ref s 0) #\-)
;;           (~a "-(" s ")")
;;           (~a "-" s)))
             
;;     (define (par u #:use [wrap paren] #:wrap-fractions? [wrap-fractions? #f]
;;                  #:exponent-base? [exponent-base? #f]) ; wrap if (locally) necessary
;;       (when debugging? (displayln (list 'par u 'orig original? 'wrap wrap 'exponent-base exponent-base?)))
;;       (math-match u
;;         [(list 'red   u) (~red  (par u))]           ; red color
;;         [(list 'blue  u) (~blue (par u))]           ; blue color
;;         [(list 'paren u ...) (~explicit-paren (map v~ u))] ; explicit parens (tex)
;;         [α    #:when (and wrap-fractions? (not (integer? α))) (wrap (~frac α))] ; XXX
;;         [α    #:when (not (integer? α)) (~frac α)] ; XXX
;;         [r    #:when (>= r 0)           (~num r)]
;;         [r.bf #:when (bf>= r.bf (bf 0)) (~a r.bf)]
;;         [x                              (~a (~var x))]
;;         ; infix operators and relations
;;         ; [(⊗ 1 v)     (exponent-wrap (par v))] ; xxx
;;         [(⊗  1 v)                       (exponent-wrap        (~a  (v~ v original?)))]
;;         [(⊗ -1 v) #:when exponent-base? (exponent-wrap        (~a "(-"        (v~ v #t) ")"))]
;;         [(⊗ -1 v) #:when original?      (let ([s (prefix-minus (v~ v))])
;;                                           (if (eqv? (string-ref s 0) #\-) (wrap s) (exponent-wrap s)))] ; XX
;;         [(⊗ -1 v)                       (exponent-wrap        (~a "(-"        (v~ v #t) ")"))]
;;         [(⊗ u v) #:when exponent-base?  (exponent-wrap (paren (~a (par u) (implicit* u v) (par v))))] ; TODO XXX ~ two layers
;;         [(⊗ u v) #:when original?       (let ([s (~a      (v~ u)  (implicit* u v) (par v))])
;;                                           (if (eqv? (string-ref s 0) #\-) (wrap s) (exponent-wrap s)))] ; XXX
;;         [(⊗ u v)                        (exponent-wrap (~a (par (v~ u)) (implicit* u v) (par v)))]
;;         [(⊕ _ __)    (wrap u)]
;;         [(list* '- _ __) (wrap u)]
;;         [(And u v)   (~a (par u) " " (~sym 'and) " " (par v))]
;;         [(Or u v)    (~a (par u) " " (~sym 'or)  " " (par v))]
;;         [(Equal u v) (~a (par u) " " (~sym '=)   " " (par v))]
;;         ; powers
;;         [(Expt u 1/2) #:when (output-sqrt?) ((output-format-sqrt) u)]
;;         [(Expt u -1)    (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                         (wrap (format/ 1 (par u #:use quotient-sub)))]
;;         ; unnormalized power of a power
;;         [(Expt (and (Expt u v) w) w1) (~a ((output-sub-exponent-wrapper) ; braces for tex otherwise nothing
;;                                            (v~ w)) 
;;                                           (~sym '^) ((output-sub-exponent-wrapper)
;;                                                      (fluid-let ([original? #t])
;;                                                        (par v #:use exponent-sub
;;                                                             #:wrap-fractions? #t))))]
;;         [(Expt u p)   (~a (par u #:use base-sub)
;;                           (~sym '^) ((output-sub-exponent-wrapper)
;;                                      ((output-format-function-symbol)
;;                                       (fluid-let ([original? #t])
;;                                          (par p #:use exponent-sub)))))]
;;         [(Expt u α)     #:when (= (%numerator α) -1) ; -1/p
;;                         (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                         (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub))]
;;         [(Expt u v)   (~a (par u #:use base-sub)
;;                           (~sym '^) ((output-sub-exponent-wrapper)
;;                                      ((output-format-function-symbol)
;;                                       (fluid-let ([original? #t])
;;                                         (par v #:use exponent-sub #:wrap-fractions? #t)))))]
;;         [(Log u)      ((output-format-log) u)]
;;         [(Log u v)    ((output-format-log) u v)]
;;         [(Up u v)    ((output-format-up)  u v)]
        
;;         [(app: f us) #:when (memq f '(< > <= >=))
;;                      (match us [(list u v) (~a (v~ u) (~relop f) (v~ v))])]
;;         ; unnormalized quotient
;;         [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                        (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
;;         ; unormalized sqrt
;;         [(list 'sqrt u)   ((output-format-sqrt) u)]
;;         ; unnormalized root
;;         [(list 'root u v) ((output-format-root) u v)]
;;         ; unnormalized diff
;;         [(list 'diff (list 'sqrt u) x)
;;          #:when (member x (output-differentiation-mark))
;;          (~a "(" ((output-format-sqrt) u) ")'")]
;;         [(list 'diff f)
;;          #:when (symbol? f)                              (~a (~sym f) "'")]
;;         [(list 'diff (list f x) x)
;;          #:when (and (symbol? f) (symbol? x))            (~a (~sym f) "'(" (~var x) ")")]
;;         [(list 'diff u x)
;;          #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
;;         [(list 'diff u  x)                               (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]

;;         [(list 'percent u) (~a (v~ u) (~sym '|%|))]
;;         [(list 'abs u) ((output-format-abs) u)] 
;;         [(list 'vec u) (~a "\\overrightarrow{" (v~ u) "}")] ; TODO: only for TeX 
;;         [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
;;         [(list 'hat u) (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX 

;;         ; applications
;;         [(app: f us) (let ()
;;                        (define arguments
;;                          (apply string-append (add-between (map v~ us) ",")))
;;                        (define head ((output-format-function-symbol) f))
;;                        (~a head app-left arguments app-right))]
;;         [_  (wrap u)]))
;;     (define (t1~ u) ; term 1 aka first term in a sum
;;       (when debugging? (displayln (list 't1 u)))
;;       (math-match u
;;                   [(list 'red   u) (~red  (t1~ u))]
;;                   [(list 'blue  u) (~blue (t1~ u))]           ; blue color
;;                   [(list 'paren u ...) (~explicit-paren (map t1~ u))] ; explicit parens (tex)

;;                   ; unnormalized and normalized quotients
;;                   [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                                  (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
;;                   [(Quotient u v) #:when (and  (output-use-quotients?) (not (rational? v)))
;;                                   (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                                   (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
;;                   [(⊗  1 u)                       (~a                          (v~ u))]
;;                   [(⊗ -1 u)                       (prefix-minus (v~ u))]
;;                   ; integer
;;                   ; Explicit multiplication between integers
;;                   [(⊗  p q)                       (~a (~num p)  (~sym '*) (par q))]
;;                   ; [(⊗  p u) #:when (negative? p)  (~a (~sym '-) (~num (abs p)) (v~ u))] ; 
;;                   ; [(⊗  p u) #:when (positive? p)  (~a           (~num (abs p)) (v~ u))]
;;                   ; rationals (non-integer)
;;                   ; Explicit multiplication between rationals
;;                   [(⊗  α β)                       (~a (~num α) (~sym '*) (par β))]                  
;;                   ; problem: if u is a number we need an explicit *
;;                   ; [(⊗  α u) #:when (negative? α)  (~a (~sym '-) (~num (abs α)) (v~ u))] 
;;                   ; [(⊗  α u) #:when (positive? α)  (~a           (~num (abs α)) (v~ u))]
;;                   ; other reals
;;                   [(⊗  r s)                       (~a     (~num r) (~sym '*) (par s))]
;;                   ; explicit multiplication for powers with numbers as base
;;                   [(⊗ r (and (Expt (num: s) u) v)) #:when (negative? r) (~a "-" (~num (abs r)) (~sym '*) (v~ v))] ; XXX
;;                   [(⊗ r (and (Expt (num: s) u) v)) #:when (positive? r) (~a     (~num (abs r)) (~sym '*) (v~ v))]
                  
;;                   [(⊗  r u) #:when (negative? r)  (~a (~sym '-) (~num (abs r)) (implicit* r u) (par u))] ; XXX
;;                   [(⊗  r u) #:when (positive? r)  (~a           (~num (abs r)) (implicit* r u) (par u))] ; XXX
;;                   [u                                                           (v~ u) ]))
;;     (math-match u
;;       [(? string? u) u]
;;       [(list 'red   u) (~red  (v~ u))]
;;       [(list 'blue  u) (~blue (v~ u))]           ; blue color
;;       [(list 'paren u ...) (~explicit-paren (map v~ u))] ; explicit parens (tex)
;;       [(list 'formatting options u)
;;        (let loop ([os options])
;;          (match os
;;            ['()                                   (v~ u)]
;;            [(list (list 'use-quotients? v) os ...) (parameterize ([output-use-quotients? v]) (loop os))]
;;            [_                                     (error 'verbose-formatting (~a "unknown option" os))]))]
;;       [α           (~frac α)]
;;       [r           (~num r)]
;;       [r.bf        (bigfloat->string r.bf)]
;;       [x           (~a (~var x))]
;;       ; unnormalized and normalized quotients
;;       [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                      (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
;;       [(Quotient u v) #:when (and  (output-use-quotients?) (not (rational? v)))
;;                       (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                       (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
;;       [(Expt u α)     #:when (and (output-root?) (= (%numerator α) 1) ((output-format-root) u (/ 1 α))) ; α=1/n
;;                       ((output-format-root) u (/ 1 α))] ; only used, if (output-format-root) returns non-#f 
;;       [(Expt u α)     #:when (= (%numerator α) -1) ; -1/p
;;                       (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                       (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub #:exponent-base? #t))]
;;       ; The ⊘ pattern will match even when u=1. Quotient and ⊘ will rewrite unnormalized u v.
;;       [(⊘ u v)       (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
;;                       (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
      
;;       ; mult
;;       [(⊗  1 v)                                               (~a             (v~ v))]
;;       [(⊗ -1 α) #:when (negative? α)                          (~a "-" (paren  (v~ α)))]
;;       [(⊗ -1 x)                                               (~a "-"         (v~ x))]
;;       [(⊗ -1 v)                                               (~a "-" (paren  (v~ v)))]      
;;       [(⊗ -1 p v) #:when (and original? (negative? p))        (displayln (list "A" p v (⊗ p v)))
;;                                                               (~a "-" (paren  (v~ (⊗ p v) #f)))]   ; wrong
;;       ; [(⊗ -1 p v) #:when                (negative? p)         (~a "-" (paren  (v~ (⊗ p v) #f)))] ; wrong
;;       [(⊗ -1 v)                                        (paren (~a "-"         (v~ v)))]
;;       ; Explicit multiplication between integers
;;       [(⊗ p q) #:when original?           (~a (~num p) (~sym '*) (par q))]
;;       [(⊗ p q) #:when (not (negative? p)) (~a (~num p) (~sym '*) (par q))]
;;       [(⊗ p q) #:when      (negative? p)  (~a "(" (~num p) ")" (~sym '*) (par q))]
;;       ; An implicit multiplication can not be used for fractions 
;;       ;[(⊗ p v)  #:when (negative? p)        (~a "-" (~num (abs p)) implicit-mult (par v #:use paren))]
;;       ;[(⊗ p v)  #:when (positive? p)        (~a     (~num (abs p)) implicit-mult (par v #:use paren))]
;;       ;[(⊗ α u)  #:when (= (numerator α)  1) (~a   "\\frac{" (v~ u) "}{"     (~num (/      α))  "}")]
;;       ;[(⊗ α u)  #:when (= (numerator α) -1) (~a   "\\frac{" (v~ u) "}{" "-" (~num (/ (abs α))) "}")]
;;       ; Implicit multiplication only if we have a symbols as base
;;       [(⊗ r (and (Expt (var: x) u) v)) #:when (negative? r) (if original?
;;                                                                 (~a            "-" (~num (abs r))   implicit-mult (v~ v #t))
;;                                                                 (~a (paren (~a "-" (~num (abs r)))) implicit-mult (v~ v #t)))] ; XXXXX *
;;       [(⊗ r (and (Expt (var: x) u) v)) #:when (positive? r) (~a                    (~num (abs r))   implicit-mult (v~ v #t))]
;;       ; Implicit multiplication between numbers and variables
;;       [(⊗ r x)  (~a (~num r) (~var x))] ; XXXX

;;       ; Use explicit multiplication for fractions
;;       [(⊗ r- (⊗ u v))  #:when (not (equal? '(*) v))
;;                       (~a "-" (~num (abs r-)) (implicit* r- u) (v~ (argcons '* u v)))]
;;       [(⊗ r+ (⊗ u v))  #:when (not (equal? '(*) v))
;;                       (~a    (~num (abs r+))  (implicit* r+ u) (v~ (argcons '* u v)))] ; XXX
;;       [(⊗ r- v)       (define w (if original? values paren))
;;                       (~a  (w (~a "-" (~num (abs r-)))) (implicit* r- v) (par v #:use paren))] ; XXX
;;       [(⊗ r+ v)       (~a     (~num (abs r+)) (implicit* r+ v) (par v #:use paren))] ; XXX
      
;;       [(⊗ u v)  #:when (not (equal? '(*) v))    (~a (par u) (implicit* u v)  (par v))]
;;       ; plus
;;       [(⊕ u r)              (if (negative? r)
;;                                 (~a (t1~ u)  (~sym '-) (~num (abs r)))
;;                                 (~a (t1~ u)  (~sym '+) (~num (abs r))))]
;;       [(⊕ u (⊗ -1 v))       (~a (t1~ u)  (~sym '-) (v~ v))]
;;       ; Unnormalized (in a normalized expression only the first factor can be a number)
;;       [(⊕ u (⊗  r s))        #:when (negative? r) (~a (t1~ u)  (~sym '-) (~num (abs r)) (~sym '*) (par s))]
;;       [(⊕ u (⊗  r s))        #:when (positive? r) (~a (t1~ u)  (~sym '+) (~num (abs r)) (~sym '*) (par s))]
;;       ; previous two rules ensure that v is non-empty
;;       [(⊕ u (⊗  r (⊗ s v)))  #:when (negative? r) 
;;                             (~a (t1~ u)  (~sym '-) (~num (abs r)) (~sym '*) (par s) (~sym '*) (v~ v))]
;;       [(⊕ u (⊗  r (⊗ s v)))  #:when (positive? r) 
;;                              (~a (t1~ u) (~sym '+) (~num (abs r)) (~sym '*) (par s) (~sym '*) (v~ v))]
;;       ;
;;       [(⊕ u (⊗  r v))       #:when (negative? r)
;;                             (~a (t1~ u)  (~sym '-) (v~ (⊗ (abs r) v)))]
;;       [(⊕ u (⊗  r v))       #:when (positive? r) 
;;                             (~a (t1~ u)  (~sym '+) (v~ (⊗ r v)))]
;;       [(⊕ u (⊕ (⊗ -1 v) w)) (~a (t1~ u)  (~sym '-) (v~ (argcons '+ v w)))]
;; ;      [(⊕ u (⊕ (⊗  r v) w)) #:when (negative? r) (displayln (list 'EEE r v))
;; ;                            (~a (t1~ u)  (~sym '-) (v~ (argcons '+ (list '* (abs r) v) w)))]
;; ;      [(⊕ u (⊕ (⊗  r v) w)) #:when (positive? r) (displayln (list 'FFF r v))
;; ;                            (~a (t1~ u)  (~sym '+) (v~ (argcons '+ (list '* (abs r) v) w)))]

;;       ; TODO: Problem: If v is a negative number, we need a paren around v.
;;       ;; [(⊕ u (⊕ (⊗  r v) w)) #:when (negative? r) (displayln (list 'EEE r v))
;;       ;;                       (~a (t1~ u)  (~sym '-) (~num (abs r)) (implicit* r v) (v~ (argcons '+ v w)))]
;;       ;; ; TODO: Problem: If v is a negative number, we need a paren around v.
;;       ;; [(⊕ u (⊕ (⊗  r v) w)) #:when (positive? r)  (displayln (list 'FFF r v))
;;       ;;                       (~a (t1~ u)  (~sym '+) (~num (abs r)) (implicit* r v) (v~ (argcons '+ v w)))]
;;       [(⊕ u v)              (match v
;;                               [(? number? r)               #:when (negative? r)  (~a (t1~ u) (v~ v))]
;;                               [(list* '* (? number? r) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
;;                               [(list* '+ (? number? r) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
;;                               [(list* '+ (list* '* (? number? r) _) _)  #:when (negative? r)  (~a (t1~ u) (v~ v))]
;;                               [_                                                 (~a (t1~ u)  (~sym '+) (v~ v))])]
;;       ; minus (doesn't appear in normalized expressions)
;;       [(list  '- u)          (~a (~sym '-) (par u #:use paren))]
;;       [(list* '- u v)        (~a (t1~ u) (~sym '-)
;;                                  (par (match v
;;                                         [(list v)   v]
;;                                         [(list* vs) (cons '+ vs)])
;;                                       #:use paren))]
;;       ; other
;;       [(And (Less u v) (Less u1 v1))           #:when (equal? v u1)
;;        (~a (par u) " " (~sym '<) " " (par v) " " (~relop '<) " " (par v1))]
;;       [(And (LessEqual u v) (Less u1 v1))      #:when (equal? v u1)
;;        (~a (par u) " " (~sym '<=) " " (par v) " " (~relop '<) " " (par v1))]
;;       [(And (LessEqual u v) (LessEqual u1 v1)) #:when (equal? v u1)
;;        (~a (par u) " " (~sym '<=) " " (par v) " " (~relop '<=) " " (par v1))]
;;       [(And (Less u v)      (LessEqual u1 v1)) #:when (equal? v u1)
;;        (~a (par u) " " (~sym '<)  " " (par v) " " (~relop '<=) " " (par v1))]
      
;;       [(And u v)            (~a (par u) " " (~sym 'and) " " (par v))]
;;       ; todo: if u or v contains And or Or in u or v then we need parentheses as in the And line
;;       [(Or u v)             (~a (v~ u) " " (~sym 'or) " " (v~ v))]
;;       [(list  '= v) (~a (~sym '=) (v~ v))]
;;       [(list* '= us) ; handle illegal = with multiple terms
;;        (string-append* (add-between (map (λ (u) (v~ u #t)) us) (~a " " (~relop '=) " ")))]
;;       [(Equal u v)        (~a (v~ u #t)  " " (~relop '=) " " (v~ v #t))] ; never reached!!
;;       ; [(⊖ u v)     (~a (par u) "-" (v~ v))]
;;       ; [(⊘ u v)     (~a (par u) (~sym '/) (par v))]
;;       [(Expt u 1/2) #:when (output-sqrt?) ((output-format-sqrt) u)]
;;       ; unnormalized power of a power
;;       [(Expt (and (Expt u v) w) w1)   (~a ((output-sub-exponent-wrapper)
;;                                           (v~ w)) 
;;                                          (~sym '^) (fluid-let ([original? #t])
;;                                                      ((output-sub-exponent-wrapper)
;;                                                       (par w1 #:use exponent-sub
;;                                                            #:wrap-fractions? #t))))]
;;       [(Expt u v)  (~a (par u #:exponent-base? #t) (~sym '^) (fluid-let ([original? #t])
;;                                            ((output-sub-exponent-wrapper)
;;                                             (par v #:use exponent-sub
;;                                                  #:wrap-fractions? #t))))]
;;       ; Unnormalized
;;       [(list 'sqr u) (v~ `(expt ,u 2))]
      
;;       ;   handle sqrt first
;;       [(list 'diff (list 'sqrt u) x)
;;        #:when (member x (output-differentiation-mark))
;;        (~a "(" ((output-format-sqrt) u) ")'")]      
;;       [(list 'diff f)
;;        #:when (symbol? f)                     (~a (~sym f) "'")]
;;       [(list 'diff (list f x) x)
;;        #:when (and (symbol? f) (symbol? x))   (~a (~sym f) "'(" (~var x) ")")]
;;       [(list 'diff u x)
;;        #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
;;       [(list 'diff u  x)                      (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]
      
;;       [(Equal u v) (~a (v~ u #t) (~sym '=) (v~ v #t))]
;;       [(Log u)     ((output-format-log) u)]
;;       [(Log u v)   ((output-format-log) u v)]
;;       [(Up u v)    ((output-format-up)  u v)]
;;       [(Piecewise us vs)    (string-append*
;;                              (append (list "\\begin{cases}\n")
;;                                      (for/list ([u us] [v vs])
;;                                        (~a (v~ u) " & " (v~ v) "\\\\\n"))
;;                                      (list "\\end{cases}")))]
;;       [(list 'sqrt u)   ((output-format-sqrt) u)]   ; unnormalized sqrt
;;       [(list 'root u v) ((output-format-root) u v)] ; unnormalized root
;;       [(list 'percent u) (~a (v~ u) (~sym '|%|))]

;;       [(list 'abs u) ((output-format-abs) u)] 
;;       [(list 'vec u) (~a "\\overrightarrow{" (v~ u) "}")] ; TODO: only for TeX 
;;       [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
;;       [(list 'hat u) (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX 

;;       [(app: f us) #:when (memq f '(< > <= >=))
;;                    (match us [(list u v) (~a (v~ u) (~sym f) (v~ v))])]
;;       [(app: f us) (let ()
;;                      (define arguments
;;                        (apply string-append (add-between (map v~ us) ",")))
;;                      (define head ((output-format-function-symbol) f))
;;                      (~a head app-left arguments app-right))]
;;       [_ (display u)
;;          (error 'verbose~ (~a "internal error, got: " u))]))

;;   ((output-wrapper) (v~ u #t)))

;; (define (reverse-plus u)
;;   (define r reverse-plus)
;;   (match u
;;     [(list* '+ us) (list* '+ (reverse us))]
;;     [(list* op us) (list* op (map r us))]
;;     [u             u]))

;; (define (~ u)
;;   (match (output-terms-descending?)
;;     [#t (verbose~ (reverse-plus u))]
;;     [#f (verbose~ u)]))

;; (module+ test
;;   (check-equal? (verbose~ '(- (- x 3))) "-(x-3)")
;;   (parameterize ([output-implicit-product? #t])
;;     (check-equal? (verbose~ (expand (Expt (⊕ x 1) 3))) "1+3x+3x^2+x^3"))
;;   (check-equal? (verbose~ (Sin (⊕ x -7))) "sin(-7+x)")
;;   (check-equal?
;;    (verbose~ (normalize '(* (sin (+ x -7)) (+ (cos (+ x -7)) (asin (+ x -7))))))
;;    "sin(-7+x)*(asin(-7+x)+cos(-7+x))")
;;   (check-equal? (parameterize ([bf-precision 100]) (verbose~ pi.bf))
;;                 "3.1415926535897932384626433832793")
;;   (check-equal? (verbose~ (Cos (⊗ 1/6 @pi))) "sqrt(3)/2")
;;   (check-equal? (verbose~ '(expt x -1/2)) "1/sqrt(x)")
;;   ; maybe we should just output (1/2)^(-2) for unnormalize forms?
;;   (check-equal? (verbose~ '(expt 1/2 -2)) "(1/2)^(-2)")
;;   ; --- MMA
;;   (use-mma-output-style)
;;   (check-equal? (~ (Sin (⊕ x -7))) "Sin[-7+x]")
;;   (use-default-output-style)
;;   (check-equal? (~ (Sin (⊕ x -7))) "sin(-7+x)")
;;   (check-equal? (~ '(* -1 x)) "-x")
;;   (check-equal? (~ '(+ (* -1 x) 3)) "-x+3")
;;   (check-equal? (~ '(+ (expt x 2) (* -1 x) 3)) "x^2-x+3")
;;   (check-equal? (~ (normalize '(/ x (- 1 (expt y 2))))) "x/(1-y^2)")
;;   (check-equal? (~ '(* 2 x y)) "2*x*y")
;;   ; —–- TeX
;;   (use-tex-output-style)
;;   (check-equal? (~ 4)   "$4$")
;;   (check-equal? (~ 2/3) "$\\frac{2}{3}$")
;;   (check-equal? (~ (normalize '(/ x (- 1 (expt y 2))))) "$\\frac{x}{1-y^{2}}$")
;;   (check-equal? (~ '(* -8 x )) "$-8x$")
;;   (check-equal? (~ '(- 1 (+ 2 3))) "$1-(2+3)$")
;;   (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "$4(-7-a)$")
;;   (check-equal? (~ '(* 3 6)) "$3\\cdot 6$")
;;   (check-equal? (~ '(sqrt d)) "$\\sqrt{d}$")
;;   (check-equal? (~ '(* (sqrt d) a)) "$\\sqrt{d}a$")
;;   (check-equal? (~ '(* -4 (expt -1 3))) "$-4\\cdot {(-1)}^{3}$")
;;   (check-equal? (~ '(* -9 (expt x -10))) "$\\frac{-9}{x^{10}}$")
;;   (check-equal? (~ '(- (* 2 3) (* -1  4))) "$2\\cdot 3-(-4)$")
;;   (check-equal? (~ '(- (* 2 3) (* -1 -4))) "$2\\cdot 3-(-(-4))$")
;;   (check-equal? (~ (normalize '(/ x (- 13/2 (expt y 15/7))))) "$\\frac{x}{\\frac{13}{2}-y^{{\\frac{15}{7}}}}$")
;;   (check-equal? (~ (complex-expt-expand (⊗ (Sqrt -2) y @pi `a))) "$\\sqrt{2}{i{π{ay}}}$")
;;   (check-equal? (~ '(paren -3)) "${\\left(-3\\right)}$")
;;   (check-equal? (~ '(red  (paren -3))) "${\\color{red}{\\left(-3\\right)}\\color{black}}$")
;;   (check-equal? (~ '(blue (paren -3))) "${\\color{blue}{\\left(-3\\right)}\\color{black}}$")
;;   (check-equal? (~ '(paren x_1 y_1))   "${\\left(x_1,y_1\\right)}$")
;;   (parameterize ([output-root? #t]) (check-equal? (~ '(expt 2 1/3)) "$\\sqrt[3]{2}$"))
;;   ; --- Default
;;   (use-default-output-style)
;;   (check-equal? (~ '(* -1 x)) "-x")
;;   (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "4*(-7-a)")
;;   (check-equal? (~ '(+ (* -3 (- x -2)) -4)) "-3*(x-(-2))-4")
;;   (check-equal? (~ '(+ (*  3 (- x -2)) -4)) "3*(x-(-2))-4")
;;   (check-equal? (~ '(+ (*  3 (- x 2)) -4)) "3*(x-2)-4")
;;   (check-equal? (~ `(+ (expt 2 3) (* 5 2) -3)) "2^3+5*2-3")
;;   (check-equal? (~ '(+ (expt -1 2) (* 3 -1) -2)) "(-1)^2+3*(-1)-2")
;;   (check-equal? (~ '(+ 1 -2 3)) "1-2+3")
;;   (check-equal? (~ '(+ 1 (* -2 x) 3)) "1-2*x+3")
;;   (check-equal? (parameterize ([output-sqrt? #f]) (~ '(expt x 1/2))) "x^(1/2)")
;;   (check-equal? (parameterize ([output-sqrt? #t]) (~ '(expt x 1/2))) "sqrt(x)")
;;   (check-equal? (~ '(+ 1 (* 7 (expt x -1)))) "1+7/x")
;;   (check-equal? (~ '(formatting ([use-quotients? #f]) (+ 1 (* 7 (expt x -1))))) "1+7/x")
;;   (check-equal? (~ '(expt (expt 65 1/2) 2)) "sqrt(65)^2")
;;   )
  

;; ;;;
;; ;;; Examples
;; ;;;

;; (define x 'x) (define y 'y) (define z 'z) (define h 'h)

;; (define (examples)
;;   (let ()
;;     (displayln "Is tan'(x) = 1 +tan(x)^2 ?")
;;     (equal? (diff (Tan x) x) (expand (⊕ 1 (Sqr (Tan x))))))
;;   (let ()
;;     (displayln "Proof of (x^2)' = 2x.")
;;     (define (f x) (⊗ x x))
;;     (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
;;     (define Δy/h (expand (⊘ Δy h)))
;;     (displayln (limit Δy/h h 0))) ; evaluates to (* 2 x)  
;;   (let ()
;;     (displayln "Proof of (x^3)' = 3x^2")
;;     (define (f x) (⊗ x x x))
;;     (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
;;     (define Δy/h (expand (⊘ Δy h)))
;;     (displayln (limit Δy/h h 0))) ; evaluates to (* 3 (expt x 2))  
;;   (let () 
;;     (displayln "Symmetric polynomials in 4 variables")
;;     (map displayln 
;;          (map expand 
;;               (coefficient-list (for/⊗ ([xi '(x1 x2 x3 x4)]) 
;;                                        (⊕ 1 (⊗ xi x))) x))))
;;   #;'(1
;;       (+ x1 x2 x3 x4)
;;       (+ (* x1 x2) (* x1 x3) (* x1 x4) (* x2 x3) (* x2 x4) (* x3 x4))
;;       (+ (* x1 x2 x3) (* x1 x2 x4) (* x1 x3 x4) (* x2 x3 x4))
;;       (* x1 x2 x3 x4))  
;;   (let () ; Pascal's triangle
;;     (displayln "Pascal's triangle")
;;     (for/list ([n 10]) 
;;       (displayln (coefficient-list (normalize `(expt (+ x 1) ,n)) x)))
;;     (void))
;;   (let ()
;;     (let ([u (expand '(* (- x 1) (expt (- x 2) 2) (- x 4)))])
;;       (define eqn (Equal u 0))
;;       (displayln (~a "Solving: " eqn))
;;       (displayln (solve eqn x)))
;;     ; Solving: (= (+ 16 (* -36 x) (* 28 (expt x 2)) (* -9 (expt x 3)) (expt x 4)) 0)
;;     ; '(or (= x 2) (= x 2) (= x 4) (= x 1))
;;     ))

;; (module+ start
;;   (provide quote quasiquote)
;;   (require (submod ".."))
;;   (require (prefix-in old: (only-in racket/base quote quasiquote)))
;;   ; In the REPL it can be convenient to change the meaning of ' 
;;   ; to automatic normalization:
;;   (define-syntax (quote stx) 
;;     (syntax-case stx () [(_ . datum) #'(normalize (old:quote . datum))]))
;;   (define-syntax (quasiquote stx) 
;;     (syntax-case stx () [(_ . datum) #'(normalize (old:quasiquote . datum))])))

;; ; (let () (define f '(* x x)) `(* x ,f))  

;; ; This macro doesn't work as expected ... why?
;; (define-syntax (repl stx) 
;;   (syntax-case stx () 
;;     [_ (with-syntax ([req (datum->syntax stx 'require)])
;;          (syntax/loc stx (req (submod "." start))))]))

;; ;(require latex-pict pict)
;; ;(define (render u)
;; ;  (define (strip$ x) (substring x 1 (- (string-length x) 1)))
;; ;  (pict->bitmap (scale (tex-math (strip$ (tex u))) 2)))


;; ;;; Example from the REPL.

;; ; Require start makes ' automatically normalize all expressions.

;; ; (displayln "Enter the following in the REPL to redefine ' to do automatic simplification.")
;; ; (write '(require (submod "." start))) (newline)
;; ;> (require (submod "." start))
;; ;> '(+ x 1)
;; ;'(+ 1 x)
;; ;> '(+ x 1 y)
;; ;'(+ 1 x y)
;; ;> (limit '(sin x) x 0)
;; ;0
;; ;> (limit '(cos x) x 0)
;; ;1
;; ;> '(expt (+ x y) 3)
;; ;'(expt (+ x y) 3)
;; ;> (expand '(expt (+ x y) 2))
;; ;'(+ (expt x 2) (expt y 2) (* 2 x y))
;; ;> (render '(+ x 1))
;; ; ...
