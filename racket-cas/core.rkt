#lang racket
(provide (all-defined-out))
(require "parameters.rkt")
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
(module+ test
  (require rackunit math/bigfloat "parameters.rkt")
  (define normalize (dynamic-require "normalize.rkt" 'normalize))
  (define x 'x) (define y 'y) (define z 'z))

(module+ test
  (newline) (newline) (displayln "-------------------------------") (newline) (newline))

; Control Parameters
(define lazy-expt?    (make-parameter #f))
(define real-mode?    (make-parameter #t))
(define complex-mode? (make-parameter #f))
(define (complex-mode)
  (lazy-expt?    #t)  ; disable certain rules in Expt
  (real-mode?    #f)
  (complex-mode? #t))
(define (real-mode)
  (lazy-expt?    #f) ; enable certain rules in Expt
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
  (λ (stx) (syntax-case stx () [(_ id) #'(list '+ id (... ...))])))
;;; The pattern (Prod us) matches a product of the form (* u ...) and binds us to (list u ...)
(define-match-expander Prod
  (λ (stx) (syntax-case stx () [(_ id) #'(list '* id (... ...))])))


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
  (math-match* (u v)
    [(r  0) +nan.0]
    [(u  1) u]
    [(u -1) (⊖ u)]
    [(u u) 1]  ; should trigger a warning: x/x=1 is not true when x=0
    [(u  v) (⊗ u (Expt v -1))]))

(define (not-one? x) (not (equal? x 1)))

(define-match-expander ⊘
  ; Note: This matches one kind of quotient, i.e., a product with a non-one denominator.
  ; Use term-numerator/denominator so that (⊘ u v) can match '(* 3 (expt x -1) y)
  (λ (stx) (syntax-parse stx [(_ u v) #'(app numerator/denominator u (? not-one? v))]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Oslash: u v)] [_ (identifier? stx) #'Oslash:])))

(module+ test
  (displayln "TEST - OSLASH")
  (check-equal? (math-match 2/3                       [(⊘ u v) (list u v)] [_ #f]) '(2 3))  
  (check-equal? (math-match (⊘ x y)                   [(⊘ u v) (list u v)] [_ #f]) '(x y))
  (check-equal? (math-match (⊗ x (Expt (⊗ 2 y z) -1)) [(⊘ u v) (list u v)] [_ #f]) '(x (* 2 y z)))
  (check-equal? (math-match (⊘ (⊗ y 3) x)             [(⊘ u v) (list u v)] [_ #f]) '((* 3 y) x))
  (check-equal? (math-match '(* 2/3 x)                [(⊘ u v) (list u v)] [_ #f]) '((* 2 x) 3)))


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
    [(Expt u p)        #:when (negative? p) 1]
    [(Expt u (⊗ p us)) #:when (negative? p) 1]    
    [(⊗ u v)                                (⊗ (numerator u) (numerator v))]
    [_                                      u]))

(define (denominator u)
  (math-match u
    [r                                      (%denominator u)]
    [r.bf                                   (%denominator u)]
    [(Expt u p)        #:when (negative? p) (Expt u (- p))]
    [(Expt u (⊗ p us)) #:when (negative? p) (Expt u (⊗ (- p) us))]
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
                                        (loop us (cons u pos)                       neg))]))]))
                        

  
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
    
    [((Expt u v) p) (Expt u (⊗ p v))]
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
  (check-equal? (Exp (Ln 3)) 3))

  
(define (Sqr: u)
  (Expt u 2))

(define-match-expander Sqr
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqr: u)] [_ (identifier? stx) #'Sqr:])))


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
  (check-equal? (Ln       @i)     '(* @i  1/2 @pi))
  (check-equal? (Ln (⊗ -1 @i))    '(* @i -1/2 @pi))
  (check-equal? (Ln (⊗  2 @i)) '(+ (* @i  1/2 @pi) (ln 2)))
  (check-equal? (Ln (⊕  1 @i)) '(+ (* @i  1/4 @pi) (ln (expt 2 1/2))))
  )


(define (fllog10 u [v #f])
  (math-match* (u v)
    [(_ #f)    (fllog10 10 u)]
    [(r.0 s.0) (fllogb r.0 s.0)]
    [(r.0 s)   (fllogb r.0 (exact->inexact s))]
    [(r   s.0) (fllogb (exact->inexact r) s.0)]
    [(r    s)  (fllogb (exact->inexact r) (exact->inexact s))]
    [(_ _)     (error 'fllog10 (~a "got: " u " and " v))]))

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
  (check-equal? (Cos @i) '(cosh 1)))

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
  (check-equal? (Sin @i) '(* @i (sinh 1))))

(define (Cosh: u)
  (when debugging? (displayln (list 'Cosh: u)))
  (math-match u
    [0 1]
    [r.0 (cosh r.0)]
    [α #:when (negative? α) (Cosh: (- α))]
    [u   `(cosh ,u)]))

(define (Sinh: u)
  (when debugging? (displayln (list 'Sinh: u)))
  (math-match u
    [0 0]
    [r.0  (sinh r.0)]
    [α #:when (negative? α) (⊖ (Sinh: (- α)))]
    [u   `(sinh ,u)]))

(define-match-expander Cosh
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'cosh u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Cosh: u)] [_ (identifier? stx) #'Cosh:])))

(define-match-expander Sinh
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'sinh u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sinh: u)] [_ (identifier? stx) #'Sinh:])))


(define (Asin: u)
  (when debugging? (displayln (list 'Asin: u)))
  (math-match u
    [0 0]
    [1  (⊗ 1/2 @pi)]
    [1/2 (⊗ 1/6 @pi)]
    [(list '* 1/2 (list 'expt 3 1/2))               (⊗ 1/3 @pi)]
    [(Expt 2 -1/2) (⊗ 1/4 @pi)]
    [(list '* 1/2 (list 'expt 2 1/2)) (⊗ 1/4 @pi)]
    [(⊖ u) (⊖ (Asin u))] ; odd function
    [r.0 (asin r.0)]
    [_ `(asin ,u)]))

(define-match-expander Asin
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'asin u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Asin: u)] [_ (identifier? stx) #'Asin:])))

; Acos = pi/2 - Asin
(define (Acos: u)
  (when debugging? (displayln (list 'Acos: u)))
  (math-match u
    [0 (⊘ @pi 2)]
    [1 0]
    [1/2 (⊗ 1/3 @pi)]
    [(list '* 1/2 (list 'expt 3 1/2))               (⊗ 1/6 @pi)]
    [(Expt 2 -1/2) (⊗ 1/4 @pi)]
    [(list '* 1/2 (list 'expt 2 1/2)) (⊗ 1/4 @pi)]
    [(⊖ u) (⊖ @pi (Acos u))]
    [r.0 (acos r.0)]
    [_ `(acos ,u)]))

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

(define-match-expander Atan
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'atan u)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Atan: u)] [_ (identifier? stx) #'Atan:])))


(define (Tan u)
  (⊘ (Sin u) (Cos u)))

(define (Degree u)
  (⊗ (⊘ @pi 180) u))

(define (Sqrt u)
  (Expt u 1/2))

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


;;; Piecewise 

(define (Piecewise: us vs) ; assume us and vs are canonical
  (define simplify (current-simplify))
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

;;;
;;; Numeric evalution
;;;


(define euler-e        (exp 1))
(define imaginary-unit (sqrt -1))
; Given an expression without variables, N will evalutate the expression
; using Racket's standard mathematical operations.

(define (N u)
  (when debugging? (displayln (list 'N u)))
  (define (M  f F u)   (math-match   (N u)        [ r    (f r)]   [ v    (F v)]))
  (define (M2 f F u v) (math-match* ((N u) (N v)) [(r s) (f r s)] [(v w) (F v w)]))
  (define (logical-or  . xs) (for/or  ([x xs]) (equal? x #t)))
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
  ; (check-equal? (N (subst '(expt (+ x 1) 5) x @pi)) (expt (+ pi 1) 5))
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


(define (in-terms/proc u)
  (match u
    [(⊕ u v) (cons u (in-terms/proc v))]
    [u       (list u)]))

(module+ test 
  (check-equal? (in-terms/proc (normalize '(+ 1 2 x y (expt x 4) (sin x)))) 
                '(3 x (expt x 4) y (sin x))))

;;;
;;; Expressions
;;; 


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

;;;
;;; Logical Operators
;;; 

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
  (check-equal? (normalize '(and (= x 1) (= x 2) (= x 1)))       '(and (= x 1) (= x 2))))

;;;
;;; Tuples
;;;

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


;; ;;;
;; ;;; Normalization
;; ;;;


;; ; normalize will given a non-canonical form u 
;; ; return the corresponding canonical form.

;; ; Note: In normalized expressions all numbers are real.
;; ;       A complex number, say, 2+3i, is rewritten to (+ 2 (* 3 @i))


;; (define (normalize u)
;;   (when debugging? (displayln (list 'normalize u)))
;;   (define (normalize-complex-number r)
;;     (define a (real-part r))
;;     (define b (imag-part r))
;;     (if (zero? a) (⊗ @i b) (⊕ (⊗ @i b) a)))
;;   (define n normalize)
;;   (math-match u
;;     [r #:when (real? r) r]    ; fast path
;;     [r (normalize-complex-number r)]
;;     [r.bf r.bf]
;;     [#t #t]
;;     [#f #f]
;;     [x x]
;;     [(⊕ u)              (n u)]
;;     [(⊕ u v)            (⊕ (n u) (n v))]
;;     [(⊗ u)              (n u)]
;;     [(⊗ u v)            (⊗ (n u) (n v))]
;;     [(And u v)          (And (n u) (n v))]
;;     [(Or u v)           (Or (n u) (n v))]
;;     [(And u)            (And (n u))]
;;     [(Or u)             (Or  (n u))]
;;     [(Expt u v)         (Expt (n u) (n v))]
;;     [(Equal u v)        (Equal        (n u) (n v))] ; xxx
;;     [(Less u v)         (Less         (n u) (n v))]
;;     [(LessEqual u v)    (LessEqual    (n u) (n v))]
;;     [(Greater u v)      (Greater      (n u) (n v))]
;;     [(GreaterEqual u v) (GreaterEqual (n u) (n v))]    
;;     [(Ln u)             (Ln   (n u))]
;;     [(Log u)            (Log  (n u))]
;;     [(Log u v)          (Log  (n u) (n v))]
;;     [(Sin u)            (Sin  (n u))]
;;     [(Asin u)           (Asin (n u))]
;;     [(Atan u)           (Atan (n u))]
;;     [(Cos u)            (Cos  (n u))]
;;     [(Acos u)           (Acos (n u))] 
;;     [(Atan u)           (Atan (n u))] 
;;     [(Cosh u)           (Cosh (n u))]
;;     [(Sinh u)           (Sinh (n u))]
;;     [(Abs u)            (Abs  (n u))]
;;     [(Magnitude u)      (Magnitude (n u))]
;;     [(Angle u)          (Angle (n u))]
;;     [(Factorial u)      (Factorial (n u))]
;;     [(Gamma u)          (Gamma (n u))]
;;     [(Prime? u)         (Prime? (n u))]
;;     [(Odd-prime? u)     (Odd-prime? (n u))]
;;     [(Nth-prime u)      (Nth-prime (n u))]
;;     [(Random-prime u)   (Random-prime (n u))]
;;     [(Next-prime u)     (Next-prime (n u))]
;;     [(Prev-prime u)     (Prev-prime (n u))]
;;     [(Divisors u)       (Divisors (n u))]    
;;     [(Piecewise us vs)  (list* 'piecewise (map list (map n us) (map n vs)))]
;;     [(app: f us) (match u
;;                    [(list  '/ u v)    (⊘ (n u) (n v))]
;;                    [(list  '- u)      (⊖ (n u))]
;;                    [(list  '- u v)    (⊖ (n u) (n v))]
;;                    [(list  'tan v)    (Tan  (n v))]
;;                    [(list  'sqr u)    (Sqr  (n u))]
;;                    [(list  'sqrt u)   (Sqrt (n u))]
;;                    [(list  'root u m) (Root (n u) (n m))]
;;                    [(list  'exp u)    (Exp  (n u))]  
;;                    [(list  'bf u)     (number? u) (bf u)]
;;                    [(list* 'or us)    (apply Or: us)]
;;                    [_ (let ([nus (map n us)])
;;                         (if (equal? us nus)
;;                             u
;;                             (n `(,f ,@nus))))])]))

;; ;;; Make normalize available in test modules in files,
;; ;;; where the normalize module can't be required.

;; (current-normalize normalize)


;; (module+ test
;;   (displayln "TEST - normalize")
;;   (check-equal? (normalize '(+ 1 x (* (expt (sin (ln (cos (asin (acos (sqrt (tan x))))))) 2))))
;;                 (⊕ 1 x (⊗ (Expt (Sin (Ln (Cos (Asin (Acos (Sqrt (Tan x))))))) 2))))
;;   (check-equal? (normalize '(/ (- x) (+ (- x y) (exp x) (sqr x) (+ 3)))) 
;;                 (⊘ (⊖ x) (⊕ (⊖ x y) (Exp x) (Sqr x) (⊕ 3))))
;;   (check-equal? (normalize '(bf 3)) (bf 3))
;;   (check-equal? (normalize '(f (- x y))) `(f ,(⊖ x y)))
;;   (check-equal? (normalize '(log 3)) '(log 10 3))
;;   ; check that complex numbers are normalized to the form (+ a (* b @i))
;;   (check-equal? (normalize  +i)     '@i)
;;   (check-equal? (normalize 1+i)  '(+ @i 1))
;;   (check-equal? (normalize  +2i) '(* @i 2))
;;   ; check that @i appears as the first symbol in products
;;   (check-equal? (normalize '(* 2 x a z 3 y @a @z @i )) '(* @i 6 @a @z a x y z)))
