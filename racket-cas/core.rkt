#lang racket
(require racket/match math/flonum math/bigfloat 
         "parameters.rkt" "math-match.rkt" "runtime-paths.rkt"
         (prefix-in % "bfracket.rkt")
         (only-in math/number-theory factorize integer-root/remainder divides? max-dividing-power)
         (for-syntax syntax/parse racket/syntax racket/format))

(provide (except-out (all-defined-out)
                     ; These functions are dynamically required in order to avoid a cycle
                     ; in module requires. See the bottom of the file.
                     ComplexRealExpt ComplexComplexExpt RealComplexExpt ExpI Angle))

;;;
;;; Debug
;;; 

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

(module+ test
  (require rackunit math/bigfloat "parameters.rkt")
  (define normalize (dynamic-require normalize.rkt            'normalize))
  (define N         (dynamic-require numerical-evaluation.rkt 'N))
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
    [(u s)               (plus2 s u)]  ; ok since u can not be a number nor @i, we have that s <<= u
    [(u u)               (times2 2 u)]    
    [((k⊗ r u) (k⊗ s u)) (times2 (+ r s) u)]
    [((k⊗ r u) (k⊗ s v))
     #:when (<<= v u)    (plus2 s2 s1)]
    [((⊕ u v)  (⊕ _ _))  (plus2 u (plus2 v s2))]
    [((⊕ u v) _)         (plus2 u (plus2 v s2))]
    [(u (⊕ v w))         (if (<<= u v)
                             (match (plus2 u v)
                               [(cons '+ _) (match w 
                                              [(cons '+ ws) (list* '+ u v ws)]
                                              [_            (list  '+ u v w)])]
                               [u+v     (plus2 u+v w)])
                             (plus2 v (plus2 u w)))]
    [(_ _)               (list '+ s1 s2)]))

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
  (check-equal? (⊕ '(sin x) (⊗ 2 '(sin x))) '(* 3 (sin x)))
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
    [(0 u) 0] 
    [(u 0) 0]
    [(1 u) u] 
    [(u 1) u]

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
    [(-1 (⊕ u v))       (⊕ (times2 -1 u) (times2 -1 v))] ; Issue #32
    ; all recursive calls must reduce size of s1 wrt <<=
    [((⊗ u v) (⊗ _ __)) (times2 u (times2 v s2))]
    [((⊗ u v) w)        (times2 s2 s1)]
    [(u (⊗ v w))
     (if (<<= u v)
         (match (times2 u v)
           [(cons '* _) (match w 
                          [(cons '* ws) (list* '* u v ws)]
                          [_            (list  '* u v w)])]
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
  (check-equal? (⊗ x '(cos x)) '(* x (cos x)))
  (check-equal? (⊗ (⊗ x y) (Sqr (⊗ x y))) (⊗ (Expt x 3) (Expt y 3)))
  (check-equal? (⊗ 2 (Expt 2 1/2)) '(* 2 (expt 2 1/2)))
  (check-equal? (⊗ (Expt 2 1/2) 2) '(* 2 (expt 2 1/2)))
  (check-equal? (⊗ -1 (⊕ 1 x)) '(+ -1 (* -1 x)))
  (check-equal? (⊕ 1 (⊕ x -1)) 'x))





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
  (check-equal? (distribute (⊗ (⊕ x y) '(cos x))) '(+ (* x (cos x)) (* y (cos x))))
  (check-equal? (distribute (⊗ (⊕ 3 x y) 2)) '(+ 6 (* 2 x) (* 2 y)))
  (check-equal? (distribute (⊕ 1 (⊗ 2 (⊕ 3 x y)))) '(+ 7 (* 2 x) (* 2 y)))
  (check-equal? (distribute '(* 2 x (+ 1 x))) (⊕ (⊗ 2 x) (⊗ 2 (Sqr x))))
  (check-equal? (distribute '(* (+ x 1) 2)) (⊕ (⊗ 2 x) 2)))



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
    [(r     0) +nan.0]
    [(r.bf  0) +nan.0]
    [(u     1) u]
    [(u    -1) (⊖ u)]
    [(u     u) 1]  ; should trigger a warning: x/x=1 is not true when x=0
    [(u     v) (⊗ u (Expt v -1))]))

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
    [(Expt u r)        #:when (negative? r) 1]                                ; PR11
    [(Expt u (⊗ r us)) #:when (negative? r) 1]                                ; PR11
    [(⊗ u v)                                (⊗ (numerator u) (numerator v))]
    [_                                      u]))

(define (denominator u)
  (math-match u
    [r                                      (%denominator u)]
    [r.bf                                   (%denominator u)]
    [(Expt u r)        #:when (negative? r) (Expt u (- r))]         ; PR11
    [(Expt u (⊗ r us)) #:when (negative? r) (Expt u (⊗ (- r) us))]  ; PR11
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



(module+ test
  (displayln "TEST - term-numerator/denominator")
  (let-values ([(n d) (term-numerator/denominator (normalize '(+ (/ x y) 2/3)))])
    (check-equal? n '(+ 2/3 (* x (expt y -1))))
    (check-equal? d 1))
  ; test cases adapted from https://reference.wolfram.com/language/ref/NumeratorDenominator.html?view=all
  (let-values ([(n d) (numerator/denominator 2/3)])
    (check-equal? n 2)
    (check-equal? d 3))
  (let-values ([(n d) (numerator/denominator (normalize '(* (+ x -1) (+ x -2) (expt (+ x -3) -2))))])
    (check-equal? n '(* (+ -2 x) (+ -1 x)))
    (check-equal? d '(expt (+ -3 x) 2)))
  ; Is this test case correct?
  #;(let-values ([(n d) (mma-numerator/denominator 
                         (⊗ 'a (Expt 'x 'n) (Expt 'y (⊖ 'm)) (Exp (⊕ 'a (⊖ 'b) (⊗ -2 'c) (⊗ 3 'd)))))])
      (check-equal? n '(* (expt @e (+ a (* 3 d))) a (expt x n)))
      (check-equal? d '(* (expt @e (* -1 (+ (* -1 b) (* -2 c)))) (expt y m))) ; better to simplify (* -1 (+ (* -1 b) (* -2 c))))
      ))



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

    [(0 0)          'undefined]              ; todo: throw error instead?
    [(0 r)          (cond
                      [(zero?     r) +nan.0] ; TODO: is this the best we can do?
                      [(positive? r) 0]
                      [(negative? r) (error 'Expt "undefined: 0 to a negative exponent")]
                      [else          (error 'Expt: "this is unexpected")])]
    [(0 r.bf)       (cond
                      [(bfzero?     r.bf) +nan.0] ; TODO: is this the best we can do?
                      [(bfpositive? r.bf) 0]
                      [(bfnegative? r.bf) (error 'Expt "undefined: 0 to a negative exponent")]
                      [else               (error 'Expt: "this is unexpected")])]
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

    [(u  (Log u v))     v]              ; xxx - is this only true for u real?
    [(@e (Ln v))        v]
    [(@e (⊗ p (Ln v)))  (Expt v p)]
    [(@e @i)            (ExpI 1)]
    [(@e x)             `(expt @e ,x)]    
    [(@e v)             (match v
                          [(list  '*   '@i '@pi)                  (ExpI @pi)]
                          [(list  '* r '@i '@pi) #:when (real? r) (ExpI (⊗ r @pi))] 
                          [_ `(expt @e ,v)])]
    
    [(@i α)             (ExpI (⊗ 1/2 α @pi))]
    [(@i (Complex a b)) (ComplexComplexExpt Expt 0 1 a b)]
    ; we need to handle all @i cases before x is met (otherwise thus catches @i^_ 
    [(x  v)          #:when (not (eq? x '@e))            `(expt ,x ,v)]
    [((Expt u  α) β) #:when (and (integer? (* α β))
                                 (not (and (integer? α)   (even? α))))
                     (Expt u (* α β))]  ; PR11
    [((Expt u  v) p) (Expt u (⊗  p v))]
    ; [((Expt u -1) v) (Expt u (⊗ -1 v))] ; PR11 - compare NSpire
    
    [(u v)
     (cond
       [(real-mode?)  ; real mode
        (math-match* (u v)
          ;[((Expt u v) w)  (Expt u (⊗ v w))] ; This is not true, for example, (Sqrt (Sqr x))
          [((Expt u  α) β) #:when (and (integer? (* α β))
                           (even? (* α β)))
                           (Expt u (* α β))]
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
             [(equal? d 0)               (ComplexRealExpt    Expt a b c)]
             [(equal? b 0)               (RealComplexExpt    Expt a c d)]
             [else                       (ComplexComplexExpt Expt a b c d)])]
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
  (check-equal? (Exp '(* 2 (ln x))) '(expt x 2))
  
  (check-equal? (Expt (Expt x 1/2) 2) x)
  (check-equal? (Expt (Expt x 2) 1/2) '(expt (expt x 2) 1/2))
  (check-equal? (Expt (Expt x 4) 1/2) '(expt x 2)))


;;;
;;; Logarithms
;;; 

; Note: Expt and Log/Ln depend on each other, so logarithms can't be move
;       out of the core.

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
                (⊗ α (Ln: u))]     ;  ln(x^1/2) = 1/2*ln(x) but don't rewrite ln(x^3).
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
  (check-equal? (Ln (Expt x -1/2)) '(* -1/2 (ln x)))
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


;;;
;;; Convenient Powers
;;;
  
(define (Sqr: u)
  (Expt u 2))

(define-match-expander Sqr
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqr: u)] [_ (identifier? stx) #'Sqr:])))


(define (Sqrt: u)
  (Expt u 1/2))

(define-match-expander Sqrt
  (λ (stx) (syntax-parse stx [(_ u) #'(list 'expt u 1/2)]))
  (λ (stx) (syntax-parse stx [(_ u) #'(Sqrt: u)] [_ (identifier? stx) #'Sqrt:])))



(define (Root u n)
  (Expt u (⊘ 1 n)))

(module+ test
  (displayln "TEST - Sqrt")
  (check-equal? (Sqrt 0) 0) (check-equal? (Sqrt 1) 1) (check-equal? (Sqrt 4) 2))


;;;
;;; Absolute Value
;;;

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


;;;
;;; Sum and products
;;;


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

(define (free-of u v)
  ; return true if is not a complete subexpression of u, false otherwise
  (when verbose-debugging? (displayln (list 'free-of u v)))
  (define (f u)
    (and (not (equal? u v))
         (math-match u
           [r #t]
           [r.bf #t]
           [x #t]
           [(list* 'piecewise us) (andmap (lambda (ys) (f (first ys))) us)] ; consider hte piecewise function as free of v if pieces are, no matter whether conditionals are.
           [(app: _ us)             (andmap f us)]
           [_  (error 'free-of (~a "missing-case:" u v))])))
  (f u))

(module+ test
  (let () (define u (Expt (⊕ x 1) 2))
    (check-equal? (free-of u x) #f)
    (check-false (or  (free-of u x) (free-of u 1) (free-of u 2) (free-of u (⊕ x 1))))
    (check-true  (and (free-of u y) (free-of u 3) (free-of u (⊕ x 2)))))
  (check-true (free-of '(piecewise (-1 (< x 0)) (1 (>= x 0))) 'x))
  (check-false (free-of '(piecewise (x (< x 0)) (1 (>= x 0))) 'x)))

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
;;; Dynamic Requires
;;;

; Note: These dynamic-requires needs to be last.
;       Otherwise you'll risk getting "instantiate-linklet: mismatch" errors.


(define ComplexRealExpt     (dynamic-require complex.rkt 'ComplexRealExpt))
(define ComplexComplexExpt  (dynamic-require complex.rkt 'ComplexComplexExpt))
(define RealComplexExpt     (dynamic-require complex.rkt 'RealComplexExpt))
(define ExpI                (dynamic-require complex.rkt 'ExpI))
(define Angle               (dynamic-require complex.rkt 'Angle))
