#lang racket
(require (only-in "core.rkt" ⊘))  ; matches quotient with non-1 denominator
(require (for-syntax syntax/parse))
(provide use-minus-in-sums?
         implicit-product?
         implicit-minus-one-as-first-factor?
         output-root?
         output-root-as-power?
         use-sqrt-for-two-as-root-exponent?
         use-sqrt-for-half-as-exponent?
         use-quotient-for-negative-exponent?
         use-quotient-for-exponent-minus-one?
         use-quotient?
         output-floating-point-precision
         output-differentiation-mark
         output-terms-descending?

         mode
         format
         format/no-wrap
         latex
         latex-mode ; 'inline 'mathsdisplay or 'unwrapped
         )


;;;
;;; TODO
;;;   - (- x ...) with more than two arguments
;;;   - negative exponents formatted as quotients
;;;   - support big floats
;;;   - complex numbers
;;;   - integrals
;;;   - special minus sign for nspire output (maybe?)

;;;
;;; New Formatter
;;;

;;; Goals
; - support several output formats: default, latex, matehematica, nspire
; - never output more parens than needed
; - flexible options

;;; Parameters

(define use-minus-in-sums? (make-parameter #t))
; If #t:   (+ 1 -2 3 -4)  ->  1-2+3-4
; If #f:   (+ 1 -2 3 -4)  ->  1+(-2)+3+(-4)

(define implicit-product? (make-parameter #f))
; If #t:   (* 2 x) -> 2x
; If #f:   (* 2 x) -> 2*x

(define implicit-minus-one-as-first-factor? (make-parameter #t))
; If #t:   (* -1 x) -> -x
; If #f:   (* -1 x) -> -1*x (or -1x if implicit-prodcut? is #t

(define output-root? (make-parameter #f))
; If #t:   (expt u 1/n) -> root(u,n)
; If #t:   (expt u 1/n) -> u^(1/n)

(define output-root-as-power?      (make-parameter #t))
; If #t:   (root x 3) -> root(x,3)
; If #f:   (root x 3) -> x^(1/3)

(define use-sqrt-for-two-as-root-exponent? (make-parameter #t))
; If #t:   (root x 2) -> sqrt(x)
; If #f:   (root x 2) -> x^(1/2)

(define use-sqrt-for-half-as-exponent? (make-parameter #t))
; If #t:   (expt x 1/2) -> sqrt(x)
; If #f:   (expt x 1/2) -> x^(1/2)


(define use-quotient-for-negative-exponent? (make-parameter #t))
; If #t:   (expt 2 -3) -> 1/2^3
; If #f:   (expt 2 -3) -> 2^-3

(define use-quotient-for-exponent-minus-one? (make-parameter #t))
; If (use-quotient-for-negative-exponent?) is #t, then
;   If #t:   (expt 2 -1) -> 1/2   
;   If #f:   (expt 2 -1) -> 2^-1
; If (use-quotient-for-negative-exponent?) is #f, then
;            (expt 2 -1) -> 2^-1

(define use-quotient? (make-parameter #t))
; If #t:   (* x (expt y -1)) -> x/y
; If #f:   (* x (expt y -1)) -> x*y^-1


;; (define flatten-nested-sums (make-parameter #f))
;; ; If #t:   (+ 1 (+ 2 3) 4)  ->  1+2+3+4
;; ; If #f:   (+ 1 (+ 2 3) 4)  ->  1+(2+3)+4

(define output-floating-point-precision (make-parameter 4))
;; If 4:   1/3 -> 0.3333
;; If 5:   1/3 -> 0.33333
;; etc

(define output-differentiation-mark  (make-parameter '(x)))
;; If a variable, say x, is in the this list:
;;   x in list:     (diff u x)  -> (u)'
;;   x not in list: (diff u x)  -> d/dx(u)

(define output-terms-descending?      (make-parameter #f))
;; reverse terms before outputting?
;; If #t:     (+ 1 x y)  -> y+x+1
;; If #f:     (+ 1 x y)  -> 1+x+y


;;;
;;; TEST
;;;

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))

(define debug? #f)
(define (debug!) (set! debug? (not debug?)))


;;;
;;; Modes
;;;

(define modes '(default latex mathematica nspire))
(define (mode? x) (and (member x modes) #t))

(define mode (make-parameter 'default))

;;;
;;; Contexts
;;;

; terms:       first-term, inner-term, last-term
; factors:     first-factor, inner-factor, last-factor
; difference:  minuend, subtrahend        
; quotient:    denominator, numerator
; power:       base, exponent
; application: function-name, argument
; reference:   variable-name
; sqrt:        radicand

; All contexts:
; first-term inner-term last-term first-factor inner-factor last-factor minuend subtrahend        
; denominator numerator base exponent function-name argument variable-name


;; The formatting of an object depends on its context.

;; Example:  a + b + c + d    
;;   a    first-term
;;   b,c  inner-term
;;   d    last-term

;; Example:  a*b*c*d
;;   a    first-factor
;;   b,c  inner-factor
;;   d    last-factor

;; Example:  a-b
;;   a minuend
;;   b subtrahend

;; Example:  a/b
;;   a numerator
;;   b denominator

;; Example:  a^b
;;   a base
;;   b exponent

;; Example: -a
;;   a unary-minus

;; Example:  f(a,b,c)
;;   f     function-name
;;   a,b,c argument

;; Example:  sqrt(x)
;;   x     radicand

;; Example:  foo
;;   foo     variable reference

;;;
;;; VARIABLE NAMES
;;; 

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
    ['|%|  "\\%"]         ; percent    
    [_ (~a t)]))

(define (format-variable-name-for-tex x)
  (match x
    ['@pi "π"]           ; π   3.14...
    ['@i "i"]            ; i   imaginary unit
    ['@e "\\mathrm{e}"]  ; e   Eulers constant
    ['\\ "\\\\"]         ; \\  LaTeX linebreak
    [(? symbol? x)
     (define s (symbol->string x))
     (cond
       ; single letter variables are italic
       [(= (string-length s) 1)  (symbol->tex x)]
       ; identifiers with subscripts
       [(string-contains? s "_")
        (define parts           (string-split s "_"))
        (define formatted-parts (map format-variable-name-for-tex (map string->symbol parts)))
        (string-append* (add-between (map ~a formatted-parts) "_"))]
       [(string-contains? s "-")
        ; An dash in an identifer is formatted as a space
        (~a "\\mathrm{" (symbol->tex (string->symbol (string-replace s "-" "\\;"))) "}")]
       [else
        (~a "\\mathrm{" (symbol->tex x) "}")])]))

(define (format-variable-name ctx x)
  (case (mode)
    [(default) (match x ['@pi "pi"]  ['@i "i"]  ['@e "e"]  [_ (~a x)])]
    [(mma)     (match x ['@pi "Pi"]  ['@i "I"]  ['@e "E"]  [_ (~a x)])]
    [(nspire)  (match x ['@pi "@pi"] ['@i "@i"] ['@e "@e"] [_ (~a x)])]
    [(latex)   (format-variable-name-for-tex x)]
    [else (error 'format-variable-name "unknown mode")]))

;;;
;;; NUMBERS
;;;

(define (format-sign ctx x)
  ; The sign of a number x is usually -, but
  ; NSpire uses different characters for subtraction - and sign (-).
  (case (mode)
    ; [(nspire) "−"]   ; note: it looks like -, but it is a different character
    [else     "-"]))



(define (format-number ctx x)
  (when debug? (displayln (list 'format-number ctx x)))
  ;; Integers
  (define (format-zero) "0")
  (define (format-positive-integer    x) (number->string x))
  (define (format-nonnegative-integer x) (number->string x))
  (define (format-negative-integer    x) (~a (format-sign ctx x)
                                             (format-positive-integer (abs x))))
  (define (format-integer x)
    (cond [(zero? x)     (format-zero)]
          [(positive? x) (format-positive-integer x)]
          [(negative? x) (format-negative-integer x)]
          [else          (error 'format-integer "expected an integer")]))
  ;; Rational Numbers
  (define (format-numerator    x) (format-nonnegative-integer x))
  (define (format-denominator  x) (format-nonnegative-integer x))  
  (define (format-rational x)
    (define sign    (if (negative? x) (format-sign ctx x) ""))
    (define num     (numerator   (abs x)))
    (define den     (denominator (abs x)))
    (define plain   (case (mode)
                      [(latex)   (if (> den 1)
                                     (~a "\\frac{" sign num "}{" den "}")
                                     (~a x))]
                      [else      (~a sign num "/" den)]))
    plain)
  ;; Real Numbers
  (define (format-real r)
    (define precision (output-floating-point-precision))
    (define default
      (cond [(eqv? r -inf.0) "-∞"]
            [(eqv? r +inf.0) "∞"]
            ; [(and (exact? r) (> (denominator r) 1)) (format-fraction r)]
            [(exact? r) (~a r)]
            [(nan? r)   (~a r)]
            [precision  (~r r #:precision precision)]
            [else       (~a r)]))
    (case (mode)
      ; Nspire uses a different minus for signs in its output.
      ; [(nspire) (string-replace default "−" "-")]
      [else     default]))
  ;; Complex Numbers
  (define (format-complex x) (~a x))

  ;; Dispatch
  (cond
    [(integer?  x)                  (wrap (list* 'integer  ctx) x (format-integer  x))]
    [(and (exact? x) (rational? x)) (wrap (list* 'rational ctx) x (format-rational x))]
    [(real?     x)                  (wrap (list* 'real     ctx) x (format-real     x))]
    [(complex?  x)                  (wrap (list* 'complex  ctx) x (format-complex  x))]
    [else                           (error 'format-number (~a "expected a number, got: " x))]))

(define (paren x)
  (case (mode)
    [(latex) (~a "(" x ")")
             #;(~a "\\left(" x "\\right)")]
    [else    (~a "(" x ")")]))

(define (wrap ctx x unwrapped)
  (when debug? (displayln (list 'wrap ctx x unwrapped)))

  ; Note: wrap is affected by the parameter:
  ; use-minus-in-sums
  ;   If #t:   (+ 1 -2 3 -4)  ->  1-2+3-4
  ;   If #f:   (+ 1 -2 3 -4)  ->  1+(-2)+3+(-4)
  ; That is: If (use-minus-in-sums) is #t we don't need to wrap in the
  ; contexts 'inner-term and 'last-term if 

  (define (base-sub x)
    ; wraps the base of an expt-expression
    (cond
      [(and (number? x) (negative? x)) (paren x)]
      [(number? x)                     x]
      [else                            (case (mode)
                                         [(latex) (~a "{" (paren x) "}")]
                                         [else            (paren x)     ])]))

  (define (wrap-base x)
    ; wraps the base of an expt-expression
    (case (mode)
      [(latex) (~a "{" (paren x) "}")]
      [else    (paren x)]))
  
  (define (wrap-exponent x)
    ; wraps the exponent of an expt-expression
    (case (mode)
      [(latex) (if (> (string-length x) 1)
                   (~a "{" x "}")
                   x)]
      [else    (paren x)]))

  (define (wrap-numerator x)
    ; wraps the numerator of a difference
    (case (mode)
      [(latex) x]
      [else    (paren x)]))

  (define (wrap-denominator x)
    ; wraps the denominator of a difference
    (case (mode)
      [(latex) x]
      [else    (paren x)]))

  (define (wrap-radicand x)
    ; wraps the radicand of a root
    (case (mode)
      [(latex) (~a "{" x "}")]
      [else    x])) ; becomes an argument of root, so no wrapping needed
  
  ; The value x is formatted in the contex ctx.
  ; The value `unwrapped` is the result without any wrapping.
  (match ctx
    ;;; An orignal never needs wrapping.
    [(list* 'original _)    unwrapped]
    [(list* _ 'original __) unwrapped]
    ;;; NUMBERS
    [(list* (or 'integer 'rational 'real)
            (and (or 'inner-term 'last-term 'inner-factor 'last-factor 'subtrahend) top-ctx) more)
     ; only negative numbers in these contexts require wrapping
     (if (or (positive? x) (zero? x)
             (and (use-minus-in-sums?) (member top-ctx '(inner-term last-term))))
         unwrapped
         (paren unwrapped))]
    [(list* (or 'integer 'rational 'real) 'unary-minus  more)
     (if (or (positive? x) (zero? x)) unwrapped (paren unwrapped))]    
    [(list* 'rational (or 'numerator 'denominator) more)
     (paren unwrapped)]
    [(list* (or 'integer 'real) 'exponent more)
     (case (mode)
       [(latex) (wrap-exponent unwrapped)]
       [else    (if (negative? x) (wrap-exponent unwrapped) unwrapped)])]
    [(list* 'rational 'exponent more)
     (wrap-exponent unwrapped)]
    
    [(list* (or 'integer 'real) (or 'first-term 'minuend 'first-factor 'numerator 'denominator) more)
     ; no wrapping needed
     unwrapped]
    [(list* (or 'integer 'real) 'base more)
     (if (or (zero? x) (positive? x))
         unwrapped
         (wrap-base unwrapped))]
    [(list* 'rational 'base more)
     (if (and (integer? x) (or (zero? x) (positive? x)))
         unwrapped
         (wrap-base unwrapped))]
    [(list* (or 'integer 'rational 'real)
            (or 'first-term 'first-factor 'minuend 'argument 'radicand)
            more)
     unwrapped]
    [(list* 'rational more)
     (error 'wrap (~a "no explicit rule for rational in the context: " ctx))]
    ;;; SUMS
    [(list* 'sum top-ctx more)
     (case top-ctx
       [(first-term)           unwrapped]
       [(inner-term last-term) (paren unwrapped)]
       [(minuend subtrahend)   (paren unwrapped)] ; note: the minuend could be unwrapped
       [(first-factor inner-factor last-factor)
                      (if (< (length x) 2) unwrapped (paren            unwrapped))]
       [(numerator)   (if (< (length x) 2) unwrapped (wrap-numerator   unwrapped))]
       [(denominator) (if (< (length x) 2) unwrapped (wrap-denominator unwrapped))]
       [(base)        (if (< (length x) 2) (base-sub unwrapped) (paren unwrapped))]
       [(exponent) (wrap-exponent unwrapped)]
       [(argument)          unwrapped]
       [(relation-argument) unwrapped]
       [(function-name variable-name) (error 'wrap (~a "got: " x " in the context: " ctx))]
       [(unary-minus) (paren unwrapped)]
       [else (error 'wrap (~a "got: " x " in the context: " ctx))])]
    ;;; PRODUCTS
    [(list* 'product top-ctx more)
     (case top-ctx
       [(first-term inner-term last-term) unwrapped]
       [(first-factor)                    unwrapped]
       [(inner-factor last-factor) (paren unwrapped)]
       [(minuend)              unwrapped] ; note: the minuend could be unwrapped
       [(subtrahend) ; prevent: (- (* 2 3) (* -4 5))) ->"2*3--4*5"
        (if (equal? (string-ref unwrapped 0) #\-)
            (paren unwrapped) unwrapped)]
       [(first-factor inner-factor last-factor)
        (if (< (length x) 2) unwrapped (paren unwrapped))]
       [(denominator numerator)
        unwrapped]
       [(base)     (if (< (length x) 2) (base-sub unwrapped) (wrap-base unwrapped))]
       [(exponent) (wrap-exponent unwrapped)]
       [(radicand) (wrap-radicand unwrapped)]
       [(argument)          unwrapped]
       [(relation-argument) unwrapped]
       [(function-name variable-name) (error 'wrap (~a "got: " x " in the context: " ctx))]
       [(unary-minus)
        (match x
          [(list* '* u v) (if (and (number? u) (not (negative? u)))
                              unwrapped
                              (paren unwrapped))]
          [_ (error)])]
       [else (error 'wrap (~a "got: " x " in the context: " ctx))])]
    ;;; POWERS
    [(list* 'power 'exponent    top-ctx more) (wrap-exponent    unwrapped)]    
    [(list* 'power 'base        top-ctx more) (wrap-base        unwrapped)]
    [(list* 'power 'numerator   top-ctx more) (wrap-numerator   unwrapped)]
    [(list* 'power 'denominator top-ctx more) (wrap-denominator unwrapped)]
    [(list* 'power (or 'first-factor 'inner-factor 'last-factor) more)
     unwrapped]
    [(list* 'power (or 'first-term   'inner-term 'last-term 'minuend 'subtrahend) more)
     unwrapped]

    ;;; DIFFERENCES
    [(list* 'difference top-ctx more)
     (case top-ctx
       [(first-term)                                   unwrapped]
       [(inner-term last-term)                  (paren unwrapped)]
       [(minuend subtrahend)                    (paren unwrapped)] ; note: the minuend could be unwrapped
       [(first-factor inner-factor last-factor) (paren unwrapped)]
       [(numerator)                             (wrap-numerator   unwrapped)]
       [(denominator)                           (wrap-denominator unwrapped)]
       [(base)                                  (paren         unwrapped)]
       [(exponent)                              (wrap-exponent unwrapped)]
       [(argument)                                      unwrapped]
       [(relation-argument)                             unwrapped]
       [(unary-minus)                           (paren unwrapped)]
       [(function-name variable-name)
             (error 'wrap (~a "got: " x " in the context: " ctx))]
       [else (error 'wrap (~a "got: " x " in the context: " ctx))])]

    ;;; QUOTIENT
    [(list* 'quotient top-ctx more)
     (case top-ctx
       [(first-term)                                   unwrapped]
       [(inner-term last-term)                         unwrapped]
       [(minuend subtrahend)                           unwrapped] ; note: the minuend could be unwrapped
       [(first-factor inner-factor last-factor)        unwrapped]
       [(denominator numerator)                 (paren unwrapped)]
       [(base)                                  (paren unwrapped)]
       [(exponent)                                     unwrapped]
       [(argument)                                     unwrapped]
       [(relation-argument)                            unwrapped]
       [(unary-minus)                                  unwrapped]
       [(radicand)                                     unwrapped] ; ?
       [(function-name variable-name)
             (error 'wrap (~a "got: " x " in the context: " ctx))]
       [else (error 'wrap (~a "got: " x " in the context: " ctx))])]
    ;;; APPLICATIONS
    [(list* 'application 'base _) (wrap-base unwrapped)]
    [(list* 'application  _)                 unwrapped]
    
    ;;; SQUARE ROOTS
    [(list* 'sqrt top-ctx more)      unwrapped]
    [(list* 'radicand top-ctx more)  unwrapped]
    ;;; UNARY MINUS
    [(list* 'unary-minus (or 'inner-factor 'subtrahend) _) (paren unwrapped)]
    [(list* 'unary-minus 'base _)                          (wrap-base unwrapped)]
    [(list* 'unary-minus (or 'inner-term 'last-term) _)
     (if (use-minus-in-sums?) unwrapped (paren unwrapped))]
    
    [(list* _ 'first-term _)          unwrapped]
    [(list* _ 'argument __)           unwrapped]
    [(list* _ 'relation-argument __)  unwrapped]
    [(list* _ 'paren __)              unwrapped]
    
    [_
     (error 'wrap (~a "no explicit rule for: " x " in the context: " ctx))]))

(define (minus-prefixed? s)
  (and (> (string-length s) 0)
       (equal? (string-ref s 0) #\-)))

(define (format-term ctx x)
  (format-sexp ctx x))

(define (format-factor ctx x)
  (format-sexp ctx x))

(define (format-sum ctx x)
  ;; Note: Output is affected by  output-terms-descending?.
  ;;   If #t:     (+ 1 x y)  -> y+x+1
  ;;   If #f:     (+ 1 x y)  -> 1+x+y
  (when debug? (displayln (list 'format-sum ctx x)))
  ; x = (+ ...)
  ; Note: use-minus-in-sums affects the output
  ; If #t:   (+ 1 -2 3 -4)  ->  1-2+3-4
  ; If #f:   (+ 1 -2 3 -4)  ->  1+(-2)+3+(-4)
  (define rx (if (output-terms-descending?)
                 (match x [(list* '+ terms) (cons '+ (reverse terms))] [_ x])
                 x))
  (define plain
  (cond
    [(use-minus-in-sums?)     
     (match rx
       [(list '+)
        (format-number ctx 0)]
       [(list '+ first-term)
        (format-term (list* 'first-term ctx) first-term)]
       [(list '+ first-term last-term)
        (define last (format-sexp (list* 'last-term  ctx) last-term))        
        (~a (format-term (list* 'first-term ctx) first-term)
            (if (minus-prefixed? last)
                last
                (~a "+" last)))]
       [(list '+ first-term inner-terms ... last-term)
        (define first  (format-term (list* 'first-term ctx) first-term))
        (define last   (format-term (list* 'last-term  ctx) last-term))        
        (define inners (for/list ([inner-term inner-terms])
                         (format-term (list* 'inner-term ctx) inner-term)))
        (string-append*
         (append (list first)
                 (for/list ([inner inners])
                   (if (minus-prefixed? inner) inner (~a "+" inner)))
                 (list (if (minus-prefixed? last) last (~a "+" last)))))]
       [_ (error 'format-sum (~a "expected a sum, got: " x))])]
    [else  ; don't use minus in terms - i.e. introduce parens
     (match rx
       [(list '+)
        (format-number ctx 0)]
       [(list '+ first-term)
        (format-term (list* 'first-term ctx) first-term)]
       [(list '+ first-term last-term)
        (~a (format-term (list* 'first-term ctx) first-term)
            "+"
            (format-term (list* 'last-term  ctx) last-term))]
       [(list '+ first-term inner-terms ... last-term)
        (define terms
          (append (list (format-sexp (list* 'first-term ctx) first-term))
                  (for/list ([inner-term inner-terms])
                    (format-term (list* 'inner-term ctx) inner-term))
                  (list (format-term (list* 'last-term  ctx) last-term))))
        (string-append* (add-between terms "+"))]
       [_ (error 'format-sum (~a "expected a sum, got: " x))])]))
  (wrap (cons 'sum ctx) x plain))

(define (format-product ctx x)
  ; Note: implicit-minus-one-as-first-factor affects the output
  ;   If #t:   (* -1 x) -> -x
  ;   If #f:   (* -1 x) -> -1*x (or -1x if implicit-prodcut? is #t  
  (define explicit (case (mode) [(latex) "\\cdot "] [else "*"]))
  (define implicit (if (implicit-product?) "" explicit))
  (define (implicit* u v) ; returns either explicit or implicit
    (cond
      [(implicit-product?)
       (match u         
         ; first factor is a number
         [(? number? r)
          (match v
            [(? number?)             explicit]
            [(? symbol?)             implicit]
            [(list* '* v _)          (implicit* r v)]
            [(list* 'expt u1 u2)     (implicit* r u1)]
            [(list  '+    u1 u2 ...) implicit]
            [(list  'vec  u1 u2 ...) implicit]  
            [(list  'sqrt u1)        implicit]
            [(list  'sqr  u1)        implicit]
            [_                       explicit])]
         ; first factor is a symbol
         [(? symbol? x)
          (define s (~a x))
          (if (or (= (string-length s) 1)
                  (and (string-contains? s "_")
                       (>= (string-length s) 2)
                       (eqv? (string-ref s 1) #\_)))
              ; only single letter variables (possibly with an index) uses implicit 
              (match v
                [(? number? s)          explicit]
                [(? symbol? y)          implicit]
                [(list '*    u1 u2)     (implicit* x u1)]
                [(list 'expt u1 u2)     (implicit* x u1)]
                [(list '+    u1 u2 ...) implicit]
                [(list 'vec  u1 u2 ...) implicit]  
                [(list 'sqrt u1)        implicit]
                [(list 'sqr  u1)        implicit]
                [_                      explicit])
              ; other variables uses explicit
              explicit)]
         ; anything else is explicit
         [_ explicit])]
      ; if implicit products are off, always use *
      [else explicit]))
  
  (when debug? (displayln (list 'format-product ctx x)))
  ; x = (* ...)
  (define plain
    (match x
      [(list '*)
       (format-number ctx 1)]
      [(list '* first-factor)
       (format-factor (list* 'first-factor ctx) first-factor)]
      [(list '* 1 last-factor)
       (~a (format-factor (list* 'last-factor  ctx) last-factor))]
      [(list '* -1 last-factor)
       (cond
         [(implicit-minus-one-as-first-factor?)
          (define s (format-factor (list* 'first-factor 'unary-minus ctx) last-factor))           
          (~a (format-sign ctx -1)
              (if (equal? (string-ref s 0) #\-)   (~a "(" s ")")   s))]
         [else
          ; Don't use -1 use-minus-in-sums? is #f
          (define minus-one (if (use-minus-in-sums?) "-1" "(-1)"))
          (if (implicit-product?)
              (~a minus-one implicit (format-factor (list* 'last-factor ctx) last-factor))
              (~a minus-one explicit (format-factor (list* 'last-factor ctx) last-factor)))])]
      [(list '* first-factor last-factor)
       (~a (format-factor (list* 'first-factor ctx) first-factor)
           (implicit* first-factor last-factor)
           (format-factor (list* 'last-factor  ctx) last-factor))]
      [(list '* first-factor inner-factors ... last-factor)
       (define factors
         (append (list (format-factor (list* 'first-factor ctx) first-factor))
                 (for/list ([inner-factor inner-factors])
                   (format-factor (list* 'inner-factor ctx) inner-factor))
                 (list (format-factor (list* 'last-factor  ctx) last-factor))))
       ; use implicit* before converting to strings !!!
       (define factors/times
         (let loop ([fs factors]
                    [us (append (list first-factor) inner-factors (list last-factor))])
           (match fs
             [(list* u v more)
              (define X (implicit* (first us) (second us)))
              (cond
                [(equal? X implicit) (list* u implicit (loop (cons v more) (rest us)))]
                [(equal? X explicit) (list* u explicit (loop (cons v more) (rest us)))]
                [else (error 'internal-error)])]
             [(list v) (list v)]
             [(list)   '()])))
       (string-append* factors/times)]
      [_ (error 'format-product (~a "expected a product, got: " x))]))
  (wrap (cons 'product ctx) x plain))

(define (format-unary-minus ctx x)
  (when debug? (displayln (list 'format-unary-minus ctx x)))
  (define unwrapped
    (match x
      [(list '- u) (define s (format-sexp (cons 'subtrahend ctx) u))
                   (if (equal? (string-ref s 0) #\-)
                       (~a (format-sign ctx -1) "(" s ")")
                       (~a (format-sign ctx -1) s))]
      [_ (error 'format-unary-minus (~a "got: " x))]))
  (wrap (cons 'unary-minus ctx) x unwrapped))

(define (format-binary-minus ctx x)
  (when debug? (displayln (list 'format-binary-minus ctx x)))
  (define unwrapped
    (match x
      [(list '- u v) (~a (format-sexp (cons 'minuend    ctx) u)
                         "-"
                         (format-sexp (cons 'subtrahend ctx) v))]
      [_ (error 'format-binary-minus (~a "got: " x))]))
  (wrap (cons 'difference ctx) x unwrapped))

(define (format-quotient ctx x)
  (when debug? (displayln (list 'format-quotient ctx x)))
  (define unwrapped
    (match x
      [(list '/ u v)
       (define num (format-sexp (cons 'numerator   ctx) u))
       (define den (format-sexp (cons 'denominator ctx) v))
       (case (mode)
         [(latex) (~a "\\frac{" num "}{" den "}")]
         [else    (~a num "/" den)])]         
      [_ (error 'format-quotient (~a "got: " x))]))
  (wrap (cons 'quotient ctx) x unwrapped))

(define (format-sqrt ctx x)
  (when debug? (displayln (list 'format-sqrt ctx x)))
  (define unwrapped
    (match x
      [(list 'sqrt u)
       (define rad (format-sexp (cons 'radicand ctx) u))
       (case (mode)
         [(latex) (~a "\\sqrt{" rad "}")]
         [(mma)   (~a "Sqrt[" rad "]")]
         [else    (~a "sqrt(" rad ")")])]
      [_ (error 'format-sqrt (~a "got: " x))]))
  (wrap (cons 'sqrt ctx) x unwrapped))

(define (format-sqr ctx x)
  (when debug? (displayln (list 'format-sqr ctx x)))
  (match x
    [(list 'sqr u)
     (format-expt ctx (list 'expt u 2))]
    [_ (error 'format-sqr (~a "got: " x))]))


(define (format-root ctx x)
  ; Note: output-root-as-power? affects the output.
  ;   If #t:   (root 3 x) -> root(3,x)
  ;   If #f:   (root 3 x) -> x^(1/3)
  ; Note: KAS can't parse root(3,x) so x^(1/3) is used for KAS.  
  (when debug? (displayln (list 'format-root ctx x)))
  (match x
    [(list 'root u v) ; u radicand, v exponent
     (case (output-root-as-power?)
       [(#t) (define rad (format-sexp (cons 'radicand ctx) u))
             (define n   (format-sexp (cons 'exponent ctx) v))
             (define unwrapped
               (case (mode)
                 [(latex) (if (and (equal? v 2)
                                   (use-sqrt-for-two-as-root-exponent?))
                              (~a "\\sqrt{"        rad "}")
                              (~a "\\sqrt[" n "]{" rad "}"))]
                 [(mma)   (if (and (equal? v 2)
                                   (use-sqrt-for-two-as-root-exponent?))
                              (~a "Sqrt["          rad "]")
                              (~a "Root[" rad  "," n   "]"))]
                 [else    (if (and (equal? v 2)
                                   (use-sqrt-for-two-as-root-exponent?))
                              (~a "sqrt("          rad ")")
                              (~a "root(" rad  "," n   ")"))]))
             (wrap (cons 'root ctx) x unwrapped)]
       [(#f) (define pow `(expt u (if (number? v) (/ 1 v) `(/ 1 ,v))))
             (format-expt ctx pow)])]
    [_ (error 'format-root (~a "got: " x))]))

(define (unit-fraction? x)
  (and (number? x) (exact? x) (rational? x) (= (numerator x) 1) (> (denominator x) 1)))

(define (syntactically-negative? u)
  (or (and (number? u) (negative? u))
      (match u
        [(list '- v) #t]
        [_           #f])))

(define (syntactically-change-sign u)
  (cond
    [(and (number? u) (negative? u)) (- u)]
    [else                            (match u
                                       [(list '- v) v]
                                       [_           `(- ,u)])]))

(define (format-expt ctx x)
  ; Note: output-root? affects the output
  ;   If #t:   (expt u 1/n) -> root(u,n)
  ;   If #t:   (expt u 1/n) -> u^(1/n)
  (when debug? (displayln (list 'format-expt ctx x)))  
  (match x
    ;; Root Exponents
    [(and (list 'expt u 1/2)
          (? (λ (_) (use-sqrt-for-half-as-exponent?))))
     (format-sqrt ctx (list 'sqrt u))]
    [(and (list 'expt u (? unit-fraction? 1/n))
          (? (λ (_) (output-root?))))
     (format-root ctx (list 'root u (/ 1 1/n)))]
    ;; Negative Exponents
    [(and (list 'expt u -1) 
          (? (λ (_) (and (use-quotient-for-exponent-minus-one?)
                         (use-quotient-for-negative-exponent?)))))
     (format-quotient ctx `(/ 1 ,u))] ; rewrite to quotient
    ;; Negative Exponents
    [(and (? (λ (_) (use-quotient-for-negative-exponent?)))
          (list 'expt u (? syntactically-negative? v)))
     (define -v (syntactically-change-sign v))
     (format-quotient ctx `(/ 1 (expt ,u ,-v)))] ; rewrite to quotient
    [(list 'expt u v)
     (define base (format-sexp (cons 'base     ctx) u))
     (define ex   (format-sexp (cons 'exponent ctx) v))
     (define unwrapped
       (case (mode)
         [(latex) (~a base "^" ex)]
         [else    (~a base "^" ex)]))
     (wrap (cons 'power ctx) x unwrapped)]
    [_ (error 'format-expt (~a "got: " x))]))

(define (format-function-name-for-latex s)
  (define operators '(sin cos tan log ln sqrt det))
  (match s
    ['acos "\\cos^{-1}"]
    ['asin "\\sin^{-1}"]
    ['atan "\\tan^{-1}"]
    [_ #:when (member s operators) (~a "\\" s)]
    ['<=  "\\leq "]
    ['>=  "\\geq "]
    ['≤   "≤ "]
    ['≥   "≥ "]
    ['~   "\\approx "]
    ['*   "\\cdot "]
    ['or  "\\vee "]
    ['and "\\wedge "]
    ;;; Names with 2 or more characters needs to be typeset upright.
    [_  (define t (~a s))
        (if (= (string-length t) 1) t (~a "\\text{" t "}"))]))

(define (format-function-name ctx f)
  (case (mode)
    [(latex) (format-function-name-for-latex f)]
    [(mma)   (define s (~a f))
             (if (= (string-length s) 1) s (string-titlecase s))]
    [else  (~a f)]))


(define (format-application ctx x)
  (when debug? (displayln (list 'format-application ctx x)))  
  (match x
    [(list name #:opt opt u ...)
     (define f    (format-function-name (cons 'application ctx) name))
     (define us   (map (λ (u) (format-sexp (cons 'argument ctx) u)) u))
     (define opts (format-sexp (cons 'argument ctx) opt))
     (define args  (string-append* (add-between us ",")))
     (define largs (string-append* (add-between us "}{")))
     (define unwrapped
       (case (mode)
         [(latex) (if (backslash-symbol? name)
                      (~a name "[" opts "]" "{" largs "}")  ; commands like \boxed
                      (~a f    "[" opts "]" "("  args ")"))]
         [(mma)   (~a f "[" args "]")]
         [else    (~a f "(" args ")")]))
     (wrap (cons 'application ctx) x unwrapped)]
    [(list name u ...)
     (define f    (format-function-name (cons 'application ctx) name))
     (define us   (map (λ (u) (format-sexp (cons 'argument ctx) u)) u))
     (define args (string-append* (add-between us ",")))
     (define largs (string-append* (add-between us "}{")))
     (define unwrapped
       (case (mode)
         [(latex) (if (backslash-symbol? name)
                      (~a name "{" largs "}")  ; commands like \boxed
                      (~a f    "("  args ")"))]
         [(mma)   (~a f "[" args "]")]
         [else    (~a f "(" args ")")]))
     (wrap (cons 'application ctx) x unwrapped)]
    [_ (error 'format-application (~a "got: " x))]))

(define (format-paren ctx x)
  (when debug? (displayln (list 'format-paren ctx x)))  
  (match x
    [(list* 'paren us)
     (define ss (map (λ(u) (format-sexp (cons 'paren ctx) u)) us))
     (define args (string-append* (add-between ss ",")))
     (case (mode)
       [(latex) (~a "{\\left(" args "\\right)}")]
       [(mma)   (~a "(" args ")")]
       [else    (~a "(" args ")")])]
    [_ (error 'format-paren (~a "got: " x))]))

(define (format-braces ctx x)
  (when debug? (displayln (list 'format-braces ctx x)))  
  (match x
    [(list* 'braces us)
     (define ss (map (λ(u) (format-sexp (cons 'paren ctx) u)) us))
     (define args (string-append* (add-between ss ",")))
     (case (mode)
       [(latex) (~a "{\\left\\{" args "\\right\\}}")]
       [(mma)   (~a "{" args "}")]
       [else    (~a "{" args "}")])]
    [_ (error 'format-braces (~a "got: " x))]))

(define (format-bracket ctx x)
  (when debug? (displayln (list 'format-bracket ctx x)))  
  (match x
    [(list* 'bracket us)
     (define ss (map (λ(u) (format-sexp (cons 'paren ctx) u)) us))
     (define args (string-append* (add-between ss ",")))
     (case (mode)
       [(latex) (~a "{\\left[" args "\\right]}")]
       [(mma)   (~a "[" args "]")]
       [else    (~a "[" args "]")])]
    [_ (error 'format-bracket (~a "got: " x))]))

(define color-symbols '(red green blue purple))
(define (color-symbol? s) (and (member s color-symbols) #t))

(define (format-color ctx x)
  (when debug? (displayln (list 'format-color ctx x)))  
  (match x
    [(list the-color u)
     (define s (format-sexp (cons 'paren ctx) u))
     (case (mode)
       [(latex) (~a "{\\color{" the-color "}" s "\\color{black}}")]
       [(mma)   (error 'todo-color)]
       [else    (format-application ctx x)])]
    [_ (error 'format-color (~a "got: " x))]))


(define (format-approx ctx x)
  (when debug? (displayln (list 'format-approx ctx x)))  
  (match x
    [(list* '~ us)
     (define ss (map (λ (u) (format-sexp (cons 'relation-argument ctx) u)) us))
     (define op (case (mode) [(latex) "\\approx"] [else "~"]))
     (define unwrapped (string-append* (add-between ss (~a " " op " "))))
     (wrap (cons 'relation ctx) x unwrapped)]
    [_ (error 'format-approx (~a "got: " x))]))


;;; Relations
(define relation-symbols '(Less LessEqual Greater GreaterEqual ~ =))
(define (relation-symbol? x) (and (member x relation-symbols) #t))
(define (relation-symbol->latex-name s)
  (match s
    ['<=           "≤ "]
    ['>=           "≥ "]
    ['≤            "≤ "]
    ['≥            "≥ "]
    ['~            "\\approx "]
    ['Less         "< "]      
    ['LessEqual    "≤ "]
    ['Greater      "> "]
    ['GreaterEqual "≥ "]
    [_             (~a s " ")]))
(define (relation-symbol->default-name s)
  (match s
    ['<=           "≤ "]
    ['>=           "≥ "]
    ['≤            "≤ "]
    ['≥            "≥ "]
    ['~            "~ "]
    ['Less         "< "]      
    ['LessEqual    "≤ "]
    ['Greater      "> "]
    ['GreaterEqual "≥ "]
    [_             (~a s " ")]))
(define (relation-symbol->name s)
  (case (mode)
    [(latex) (relation-symbol->latex-name s)]
    [else    (relation-symbol->default-name s)]))

(define (format-relation ctx x)
  (define who 'format-relation)
  (when debug? (displayln (list who ctx x)))  
  (match x
    [(list* relsym us)
     (define op (relation-symbol->name relsym))
     (define ss (map (λ (u) (format-sexp (cons 'relation-argument ctx) u)) us))
     (define unwrapped (string-append* (add-between ss (~a " " op))))
     (wrap (cons 'relation ctx) x unwrapped)]
    [_ (error who (~a "got: " x))]))


;; (~ '(equation (split (= a
;;                         & (+ b c (- d) \\ (+ e (- f)))
;;                         & (+ g h)
;;                         & i)))))

(define (format-split-relation ctx x)
  (define who 'format-split-relation)
  ; A split-relation can contain:
  ;   &   alignment marker
  ;   \\  linebreak
  ; Split supports only a single alignment & per line.
  (when debug? (displayln (list who ctx x)))  
  (match x
    [(list 'split (list* relsym us))
     ; In the output the & must appear before the relation operator.
     (define op  (~a " " (relation-symbol->name relsym)))
     (define &op (~a " &" (relation-symbol->name relsym)))
     (define ss (map (λ (u) (format-sexp (cons 'relation-argument ctx) u)) us))
     ; Without alignment & and linebreaks \\ we could simple do:
     ; (define unwrapped (string-append* (add-between ss (~a " " op))))
     (define v0 (first ss)) ; 
     (define vs (let loop ([us (rest us)] [ss (rest ss)])
                  (define (next [n 1]) (loop (drop us n) (drop ss n)))
                  (define (split-error)
                    (error who (~a "a split environment can't end in \\\\. Got: " x)))
                  (match us
                    ; Make sure the end isn't a linebreak \\
                    [(list  _ _ '\\)  (split-error)]
                    [(list  _   '\\)  (split-error)]
                    [(list      '\\)  (split-error)]
                    ; 
                    [(list* '& u '\\ _)  (list* &op (second ss) "\\\\\n" (next 3))]
                    [(list* '&   '\\ _)  (list* &op             "\\\\\n" (next 2))]
                    [(list* '& u     _)  (list* &op (second ss)          (next 2))]
                    [(list*    u '\\ _)  (list*  op (first  ss) "\\\\\n" (next 2))]
                    [(list*      '\\ _)  (list*                 "\\\\\n" (next 1))]                    
                    [(list*    u     _)  (list*  op (first  ss)          (next 1))]
                    [(list)              (list)])))
     (wrap-latex-environment 'split (~a (string-append* (cons v0 vs)) "\n"))]
    [_ (error who (~a "got: " x))]))

  

(define (format-hat ctx x)
  (when debug? (displayln (list 'format-hat ctx x)))  
  (match x
    [(list 'hat u)
     (define s (format-sexp (cons 'paren ctx) u))     
     (case (mode)
       [(latex) (~a "{\\hat{" s "}")]
       [else    (format-application ctx x)])]
    [_ (error 'format-hat (~a "got: " x))]))

(define (format-bar ctx x)
  (when debug? (displayln (list 'format-bar ctx x)))  
  (match x
    [(list 'bar u)
     (define s (format-sexp (cons 'paren ctx) u))     
     (case (mode)
       [(latex) (~a "{\\bar{" s "}}")]
       [else    (format-application ctx x)])]
    [_ (error 'format-bar (~a "got: " x))]))

(define (format-vec ctx x)
  (when debug? (displayln (list 'format-vec ctx x)))  
  (match x
    [(list 'vec u)
     (define s (format-sexp (cons 'paren ctx) u))     
     (case (mode)
       [(latex) (~a "{\\overrightarrow{" s "}}")]
       [else    (format-application ctx x)])]
    [_ (error 'format-vec (~a "got: " x))]))

(define (format-abs ctx x)
  (when debug? (displayln (list 'format-abs ctx x)))
  (match x
    [(list 'abs u)
     (define s (format-sexp (cons 'paren ctx) u))     
     (case (mode)
       [(latex) (~a "{\\left|" s "\\right|}")]
       [(mma)   (~a "Abs[" s "]")]       
       [else    (format-application ctx x)])]
    [_ (error 'format-abs (~a "got: " x))]))

(define (format-percent ctx x)
  (when debug? (displayln (list 'format-percent ctx x)))  
  (match x
    [(list 'percent u)
     (define s (format-sexp (cons 'paren ctx) u))
     (define unwrapped
       (case (mode)
         [(latex) (~a  s "\\%")]
         [(mma)   (~a "Percent[" s "]")]       
         [else    (~a  s "%")]))
     (wrap (cons 'percent ctx) x unwrapped)]
    [_ (error 'format-percent (~a "got: " x))]))

;; [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
;; [(list 'int u v)   (~a "\\int " (v~ u) "\\ \\textrm{d}" (v~ v))] ; TODO: only for TeX

;;; Logarithms

; Input      Default    Tex          MMA
; (log x)    log(x)     \log(x)      log(x)
; (log 2 x)  log_2(x)   \log_{2}(x)  log_2(x) 

(define (format-log ctx x)
  (when debug? (displayln (list 'format-log ctx x)))  
  (match x
    [(list 'log u)   (format-application ctx x)]
    [(list 'log u v)
     (define log-base (format-sexp (cons 'base     ctx) u))
     (define log-arg  (format-sexp (cons 'argument ctx) v))
     (case (mode)
       [(latex) (~a "log_{" log-base "}" (paren log-arg))]
       [else    (format-application ctx x)])]))

(define (format-up ctx x)
  (when debug? (displayln (list 'format-up ctx x)))  
  (match x
    [(list* 'up us)
     (define ss (map (λ(u) (format-sexp (cons 'argument ctx) u)) us))
     (define args (case (mode)
                    [(latex) (string-append* (add-between ss "\\\\"))]
                    [else    (string-append* (add-between ss ","))]))
     (case (mode)
       [(latex) (~a "{\\begin{pmatrix} " args "\\end{pmatrix}}")]
       [(mma)   (format-paren ctx (list* 'paren us))]
       [else    (format-paren ctx (list* 'paren us))])]
    [_ (error 'format-up (~a "got: " x))]))

;;; Intervals

(define (format-interval/default u)
  (define v~ format/no-wrap)
  (match u
    [(list 'ccinterval -inf.0 +inf.0) (~a "]" "-∞"   ","  "∞"   "[")]
    [(list 'ocinterval -inf.0      v) (~a "]" "-∞"   "," (v~ v) "]")]
    [(list 'cointerval u      +inf.0) (~a "[" (v~ u) "," "∞"    "[")]
    
    [(list 'ccinterval u v) (~a "[" (v~ u) "," (v~ v) "]")]
    [(list 'ocinterval u v) (~a "]" (v~ u) "," (v~ v) "]")]
    [(list 'cointerval u v) (~a "[" (v~ u) "," (v~ v) "[")]
    [(list 'oointerval u v) (~a "]" (v~ u) "," (v~ v) "[")]
    [_ (error 'default-output-interval (~a "unknown interval type, got: " u))]))
  
(define (format-interval/latex u)
  ; (displayln (list 'tex-output-interval u))
  (define v~ format/no-wrap)
  (match u
    [(list 'oointerval -inf.0 +inf.0)  (~a "]" "-∞"   "," "∞"    "[")]
    [(list 'oointerval u      +inf.0)  (~a "]" (v~ u) "," "∞"    "[")] ; for wrong options
    [(list 'oointerval -inf.0      v)  (~a "]" "-∞"   "," (v~ v) "[")]
    
    [(list 'ccinterval -inf.0 +inf.0)  (~a "[" "-∞"   ","  "∞"   "]")] ; for wrong options
    [(list 'ccinterval -inf.0      v)  (~a "[" "-∞"   "," (v~ v) "]")] ; for wrong options
    [(list 'ccinterval u      +inf.0)  (~a "[" (v~ u) "," "∞"    "]")] ; for wrong options
    
    [(list 'ocinterval -inf.0 +inf.0)  (~a "]" "-∞"   "," "∞"    "]")] ; for wrong options
    [(list 'ocinterval -inf.0      v)  (~a "]" "-∞"   "," (v~ v) "]")]
    [(list 'ocinterval u      +inf.0)  (~a "]" (v~ u) "," "∞"    "]")] ; for wrong options
    
    [(list 'cointerval -inf.0 +inf.0)  (~a "[" "-∞"   "," "∞"    "[")] ; for wrong options
    [(list 'cointerval u      +inf.0)  (~a "[" (v~ u) "," "∞"    "[")]
    [(list 'cointerval -inf.0 v)       (~a "[" "-∞"   "," (v~ v) "[")] ; for wrong options
    
    [(list 'ccinterval u v) (~a "[" (v~ u) "," (v~ v) "]")]
    [(list 'ocinterval u v) (~a "]" (v~ u) "," (v~ v) "]")]
    [(list 'cointerval u v) (~a "[" (v~ u) "," (v~ v) "[")]
    [(list 'oointerval u v) (~a "]" (v~ u) "," (v~ v) "[")]
    [_ (error 'tex-output-interval (~a "unknown interval type, got: " u))]))


(define (format-interval ctx x)
  (when debug? (displayln (list 'format-interval ctx x)))
  (case (mode)
    [(latex)  (format-interval/latex   x)]
    [else     (format-interval/default x)]))

(define (format-group ctx x)
  (define who format-group)
  (when debug? (displayln (list who ctx x)))
  (match x
    [(list* 'group us)
     (define ss (map (λ (u) (format-sexp ctx u)) us))
     (case (mode)
       [(latex)  (~a "{" (string-append* ss) "}")]
       [else     (string-append* ss)])]))

(define (format-diff ctx y)
  (when debug? (displayln (list 'format-diff ctx y)))
  (define unwrapped
    (match y
      [(list 'diff (list 'sqrt u) x)
       #:when (member x (output-differentiation-mark))    
       (define sqrt-u (format-sqrt (cons 'paren ctx) (list 'sqrt u)))
       (~a (paren sqrt-u) "'")]
      [(list 'diff (? symbol? f))
       (~a (format-function-name ctx f) "'")]
      [(list 'diff (list (? symbol? f) (? symbol? x)) x)
       (let ([f (format-function-name ctx f)]
             [x (format-variable-name ctx x)])
         (~a f "'" (paren x)))]
      [(list 'diff u x)
       #:when (member x (output-differentiation-mark))
       (~a (paren (format/no-wrap u)) "'")]
      [(list 'diff u x)
       (let ([x (format-variable-name ctx x)]
             [u (format-sexp (cons 'paren ctx) u)])
         (case (mode)
           [(latex) (~a "\\dv{" x "}" (paren u))]
           [else    (~a "d/d" x (paren u))]))]
      [_ (error 'format-diff (~a "got: " y))]))
  (wrap (cons 'diff ctx) y unwrapped))

(define (format-as-quotient ctx u v x)
  (format-quotient ctx `(/ ,u ,v)))

(define (format-string ctx u)
  (case (mode)
    [(latex) (~a "\\textrm{" u "}")]
    [else    u]))

(define (format-sexp ctx x)
  (when debug? (displayln (list 'format-sexp ctx x)))
  (define uq (use-quotient?))
  (define (ni? x) (and (number? x) (not (integer? x))))
  (define (nr? x) (not (rational? x)))
  (match x
    [(? number?)                    (format-number         ctx x)]
    [(? symbol?)                    (format-variable-name  ctx x)]
    [(? string?)                    (format-string         ctx x)]
    [(list* '+ _)                   (format-sum            ctx x)]
    [(list* '* k _)  #:when (ni? k) (format-product        ctx x)]
    [(⊘ u (? nr? v)) #:when uq      (format-as-quotient    ctx u v x)] ; before * and /
    [(list* '* _)                   (format-product        ctx x)]
    [(list  '- _)                   (format-unary-minus    ctx x)]
    [(list  '- _ __)                (format-binary-minus   ctx x)]
    [(list  '/ _ __)                (format-quotient       ctx x)]
    [(list  'log _)                 (format-log            ctx x)]
    [(list  'log _ __)              (format-log            ctx x)]    
    [(list  'sqrt _)                (format-sqrt           ctx x)]    
    [(list  'sqr  _)                (format-sqr           ctx x)]    
    [(list  'root _ __)             (format-root           ctx x)]
    [(list  'expt _ __)             (format-expt           ctx x)]
    [(list* 'paren _)               (format-paren          ctx x)]
    [(list* 'braces _)              (format-braces         ctx x)]
    [(list* 'bracket _)             (format-bracket        ctx x)]
    [(list* 'hat _)                 (format-hat            ctx x)]
    [(list* 'bar _)                 (format-bar            ctx x)]
    [(list* 'vec _)                 (format-vec            ctx x)]
    [(list* 'abs _)                 (format-abs            ctx x)]
    [(list* 'percent _)             (format-percent        ctx x)]
    [(list* 'up _)                  (format-up             ctx x)]
    [(list* (or 'ccinterval
                'ocinterval
                'cointerval
                'oointerval) _)     (format-interval       ctx x)]
    [(list* 'diff _)                (format-diff           ctx x)]
    [(list* 'group _)               (format-group          ctx x)]
    [(list* '~ _)                   (format-approx         ctx x)]
    [(list* (? color-symbol?) _)    (format-color          ctx x)]
    [(list* (? relation-symbol?) _) (format-relation       ctx x)]
    [(list* (? symbol? _) __)       (format-application    ctx x)]
    
    [_
     (error 'format-sexp (~a "got: " x))]))

;;;
;;; FORMAT
;;;

(define (format/no-wrap x)
  (format-sexp '(original) x))

(define (format x)
  (when debug? (displayln (list 'format x)))
  (define unwrapped (format-sexp '(original) x))
  (case (mode)
    [(latex) (~a "$" unwrapped "$")]
    [else            unwrapped]))

(define ~ format)

;;;
;;; LATEX
;;;

(define (latex-mode? x) (and (member x '(inline mathdisplay unwrapped #f)) x))
(define latex-mode (make-parameter #f latex-mode?))

(define (latex extended-expr)
  (define x extended-expr)
  (define who 'latex)
  (when debug? (displayln (list who x)))
  (define unwrapped? (equal? (latex-mode) 'unwrapped))
  (parameterize ([mode 'latex] [latex-mode (or (latex-mode) 'inline)])
    (define unwrapped (format-latex '(original) x))
    (case (or unwrapped? (latex-mode))
      [(inline)       (~a "$"   unwrapped "$")]
      [(mathdisplay)  (~a "\\[" unwrapped "\\]")]
      [(#t unwrapped) unwrapped]
      [else (error who (~a "unknown latex mode, got: " (latex-mode)))])))

(define (format-latex ctx x)
  ;;; NOTES:
  ;;;   The following LaTeX constructs are not supported by MathJax
  ;;;     intertext, flalign
  
  (define org x)
  (define who 'format-latex)
  (when debug? (displayln (list who ctx x)))
  (match x
    ; equation* : single equation with no generated number
    [(list 'equation* x ...)
     (latex-mode 'mathdisplay)
     (define xs (for/list ([x x]) (format-latex (cons 'equation* ctx) x)))
     (latex-environment/newlines 'equation* xs)]
    ; equation  : single equation with a generated number  (n)
    [(list 'equation x ...)
     (latex-mode 'mathdisplay)
     (format-equation-env ctx org)]
    #;[(list 'equation x ...)
     (latex-mode 'mathdisplay)
     (define xs (for/list ([x x]) (format-latex (cons 'equation ctx) x)))
     (latex-environment/newlines 'equation xs)]
    [(list* 'split xs)
     ; split can only be used inside the other environment (not in multline though)
     ; Note: we don't update the context above - should we?
     #;(unless (and (for/or ([env '(equation equation*)]) (member env ctx))
                  (eq? (latex-mode) 'mathdisplay))
       (error who "the split environment must be used inside an environment (other than multline)"))
     (format-split ctx org)]
    [(list* 'multline xs)
     ; variation of `equation` for single formula, that doesn't fit a single line
     (latex-mode 'mathdisplay)  ; a `multline` can't be inline
     (format-multline ctx org)]
    [(list* 'gather xs)
     ; groups equations without alignment - each equation is centered horizontally
     (latex-mode 'mathdisplay)  ; a `gather` can't be inline
     (format-gather ctx org)]
    [(list* 'gathered xs)
     ; like `gather` but width = content width
     (latex-mode 'mathdisplay)  ; a `gather` can't be inline
     (format-gathered ctx org)]
    [(list* 'align xs)
     ; groups equations with alignment
     (latex-mode 'mathdisplay) ; an `align` can't be inline
     (format-align ctx org)]
    [(list* 'aligned xs)
     ; like `align` but width = content width
     (latex-mode 'mathdisplay) ; an `align` can't be inline
     (format-aligned ctx org)]
    ;; flalign is not supported by MathJax - sigh.
    ;; [(list* 'flalign xs)
    ;;  ; groups equations without alignment - each equation is centered horizontally
    ;;  (latex-mode 'mathdisplay)  ; a `flalign` can't be inline
    ;;  (format-flalign ctx org)]
    [(list* 'cases xs)
     ; several
     (latex-mode 'mathdisplay)  ; a `cases` can't be inline
     (format-cases ctx org)]
    [(list* 'array xs)
     (latex-mode 'mathdisplay)  ; a `array` can't be inline
     (format-array ctx org)]
    ;;;
    [(list 'right-brace u)
     (~a "\\left. " (format-latex ctx u) "\\right\\} ")]
    [(list 'left-brace u)
     (~a "\\left\\{ " (format-latex ctx u) "\\right. ")]    
    [(list 'braces u)
     (~a "\\left\\{ " (format-latex ctx u) "\\right\\} ")]
    [(list 'super u v)
     (~a "{ " (format-latex-literals (list u)) "}^{" (format-latex-literals (list v)) "}")]
    [(list 'sub u v)
     (~a "{ " (format-latex-literals (list u)) "}_{" (format-latex-literals (list v)) "}")]
    [(list 'limits u)    (~a "\\limits_{" (format-latex-literals (list u)) "}")]
    [(list 'limits u v)  (~a "\\limits_{" (format-latex-literals (list u)) 
                             "}^{"        (format-latex-literals (list v)) "}")]
    [(list 'sub-super (? symbol? u) v w)     
     (~a " "  (format-latex-literals (list u))
         "_{" (format-latex-literals (list v)) 
         "}^{" (format-latex-literals (list w)) "}")]
    [(list 'sub-super u v w)     
     (~a "{ "  (format-latex-literals (list u))
         "}_{" (format-latex-literals (list v)) 
         "}^{" (format-latex-literals (list w)) "}")]
    [_
     (format-sexp (cons 'original ctx) x)]))

(define (format-split ctx x)
  (define who 'format-split)
  ;; This version of split mimics the LaTeX one directly.
  ;; All & and \\ needs to be explicit.
  ; Split supports only a single alignment & per line.
  (when debug? (displayln (list who ctx x)))
  (match x
    [(list* 'split xs)
     (wrap-latex-environment
      'split (~a (format-latex-literals xs) "\n"))]
    [_
     (error who (~a "expected a (split ...), got: " x))]))

(define (format-array ctx x)
  (define who 'format-array)
  (when debug? (displayln (list who ctx x)))
  (match x
    [(list* 'array arg xs)
     (wrap-latex-environment 
      'array (~a (format-latex-literals xs) "\n")
      arg)]
    [_
     (error who (~a "expected a (split ...), got: " x))]))

(define-syntax (define-format-literal-latex-environment stx)
  (syntax-parse stx
    [(_ format-name name)
     (syntax/loc stx
       (define (format-name ctx x)
         (define who 'format-name)
         ;; This version of multline mimics the LaTeX one directly.
         (when debug? (displayln (list who ctx x)))
         (match x
           [(list* 'name xs)
            (wrap-latex-environment
             'name (~a (format-latex-literals xs) "\n"))]
           [_
            (error who (~a "expected a (" 'name " ...), got: " x))])))]))

; NOTE!!!
;   Remember to add a clause in format-latex-literals, when you add a new
;   environment type.
(define-format-literal-latex-environment format-equation-env equation)

(define-format-literal-latex-environment format-multline multline)
(define-format-literal-latex-environment format-gather   gather)   ; width = line width
(define-format-literal-latex-environment format-align    align)    ; width = line width
(define-format-literal-latex-environment format-flalign  flalign)
(define-format-literal-latex-environment format-cases    cases)

(define-format-literal-latex-environment format-gathered gathered) ; width = content width
(define-format-literal-latex-environment format-aligned  aligned)  ; width = content width


(define (backslash-symbol? x)
  (and (symbol? x) (equal? (string-ref (~a x) 0) #\\)))

(define (format-latex-literals xs)
  (define who 'format-latex-literals)
  ; The input is a list of literal latex tokens and S-expressions.
  ; The literal tokens will be output directly, and the S-expressions
  ; will be formatted by format-sexp in the context 'original.
  ; Literals:
  ;   &        alignment marker   
  ;   \\       linebreak
  ;   quad     space
  ;   strings  becomes \textrm{ }
  ; Split supports only a single alignment & per line.
  ;
  
  (when debug? (displayln (list who xs)))
  (define ss
    (let loop ([xs xs])
      (define (next) (loop (rest xs)))
      (cond
        [(null? xs) '()]
        [else
         (define x (first xs))
         (define s (match x
                     ['&                    " &"]
                     ['\\                   "\\\\\n"]
                     ['quad                 "\\quad "]
                     ['qquad                "\\qquad "]
                     [(? backslash-symbol?) (~a x)]
                     [(? string?) (~a "\\textrm{" x "}")]
                     [(list* (or 'equation 'split 'align 'aligned 'gather 'gathered 'flalign
                                 'multline 'cases 'array 'super 'sub 'sub-super 'limits
                                 'right-brace 'left-brace 'braces) _)
                      (format-latex '(original) x)]
                     [u      (format-sexp '(relation-argument) x)]))
         (cons s (next))])))
  (string-append* ss))


(define (wrap-latex-environment env body [arg #f])
  (match arg
    [#f (~a "\\begin{" env "}\n"
            body
            "\\end{"   env "}")]
    [_  (~a "\\begin{" env "}{" arg "}\n"
            body
            "\\end{"   env "}")]))

(define (latex-environment/newlines env lines)
  ; Note: \\ between lines - not after the last list
  (string-append* (append (list (~a "\\begin{" env "}\n"))
                          (add-between lines "\\\\\n")
                          (list "\n")
                          (list (~a "\\end{" env "}")))))

(module+ test
  ;; VARIABLE NAMES
  (parameterize ([mode 'default])
    (check-equal? (~ 'x)   "x")
    (check-equal? (~ 'foo) "foo"))
  (parameterize ([mode 'latex])
    (check-equal? (~ 'x)    "$x$")
    (check-equal? (~ 'foo)  "$\\mathrm{foo}$")
    (check-equal? (~ 'x_1)  "$x_1$")
    (check-equal? (~ 'x_12) "$x_\\mathrm{12}$"))

  ;; NUMBERS  
  (parameterize ([mode 'default])
    (check-equal? (map format
                       (list 0   1   -1   2   -2   1/2   -1/2   1.5   -1.5))
                  '(        "0" "1" "-1" "2" "-2" "1/2" "-1/2" "1.5" "-1.5")))
  ;; (parameterize ([mode 'nspire]) ; check the special sign for all number types
  ;;   (check-equal? (map format
  ;;                      (list 0   1   -1   2   -2   1/2   -1/2   1.5   -1.5))
  ;;                 '(        "0" "1" "−1" "2" "−2" "1/2" "−1/2" "1.5" "−1.5")))
  (parameterize ([output-floating-point-precision 4])
    (check-equal? (~ 0.12345) "0.1235"))
  
  ;; SUMS
  
  ; Different number of terms
  (check-equal? (~ '(+))         "0")
  (check-equal? (~ '(+ 1))       "1")
  (check-equal? (~ '(+ 1 2))     "1+2")
  (check-equal? (~ '(+ 1 2 3))   "1+2+3")
  (check-equal? (~ '(+ 1 2 3 4)) "1+2+3+4")
  ; Sums with one term
  (check-equal? (~ '(+  1))     "1")
  (check-equal? (~ '(+ -1))    "-1")
  ; Sums with negative terms
  (parameterize ([use-minus-in-sums? #t])
    ; If #t:   (+ 1 -2 3 -4)  ->  1-2+3-4
    ; If #f:   (+ 1 -2 3 -4)  ->  1+(-2)+3+(-4)
    (check-equal? (~ '(+ 1 -2))      "1-2")
    (check-equal? (~ '(+ 1 -2 3))    "1-2+3")
    (check-equal? (~ '(+ 1 -2 3 -4)) "1-2+3-4")
    (check-equal? (~ '(+ -1 2))      "-1+2")
    (check-equal? (~ '(+ -1 2 -3))   "-1+2-3")
    (check-equal? (~ '(+ -1 2 -3 4)) "-1+2-3+4"))
  (parameterize ([use-minus-in-sums? #f])
    ; If #t:   (+ 1 -2 3 -4)  ->  1-2+3-4
    ; If #f:   (+ 1 -2 3 -4)  ->  1+(-2)+3+(-4)
    (check-equal? (~ '(+ 1 -2))      "1+(-2)")
    (check-equal? (~ '(+ 1 -2 3))    "1+(-2)+3")
    (check-equal? (~ '(+ 1 -2 3 -4)) "1+(-2)+3+(-4)")
    (check-equal? (~ '(+ -1 2))      "-1+2")
    (check-equal? (~ '(+ -1 2 -3))   "-1+2+(-3)")
    (check-equal? (~ '(+ -1 2 -3 4)) "-1+2+(-3)+4"))
  ; Nested sums
  (check-equal? (~ '(+ 1 (+ 2 3) 4))  "1+(2+3)+4")
  (check-equal? (~ '(+ 1 (+ 2 (+ 3 4) 5) 6))  "1+(2+(3+4)+5)+6")
  ; Sums of products
  (check-equal? (~ '(+ 1 (* 2 3) (* 4 5 6)))  "1+2*3+4*5*6")
  ; Reversal of term order
  (parameterize ([output-terms-descending? #t])
    (check-equal? (~ 'x)         "x")
    (check-equal? (~ '(+ 1 x))   "x+1")
    (check-equal? (~ '(+ 1 x y)) "y+x+1"))
  (parameterize ([output-terms-descending? #f])
    (check-equal? (~ 'x)         "x")
    (check-equal? (~ '(+ 1 x))   "1+x")
    (check-equal? (~ '(+ 1 x y)) "1+x+y"))
  (parameterize ([implicit-minus-one-as-first-factor? #f] 
                 [use-minus-in-sums?                  #f])
    (check-equal? (~ '(+ 2 (* -1 -1))) "2+(-1)*(-1)"))
  
  

  ;; PRODUCTS
  
  ; Different number of factors
  (check-equal? (~ '(*))         "1")
  (check-equal? (~ '(* 2))       "2")
  (check-equal? (~ '(* 2 3))     "2*3")
  (check-equal? (~ '(* 2 3 4))   "2*3*4")
  (check-equal? (~ '(* 2 3 4 5)) "2*3*4*5")
  ; Products with one term
  (check-equal? (~ '(* 1))     "1")
  (check-equal? (~ '(* -1))    "-1")
  ; Nested Products
  (check-equal? (~ '(* 1 (* 2 3) 4))          "1*(2*3)*4")
  (check-equal? (~ '(* 1 (* 2 (* 3 4) 5) 6))  "1*(2*(3*4)*5)*6")
  ; Products of sums
  (check-equal? (~ '(*   (+ 3 4)    (+ 5 6)))      "(3+4)*(5+6)")
  (check-equal? (~ '(* 2 (+ 3 4)    (+ 5 6)))    "2*(3+4)*(5+6)")
  (check-equal? (~ '(* 2 (+ 3 4) -3 (+ 5 6)))    "2*(3+4)*(-3)*(5+6)")
  (check-equal? (~ '(* -2 (+ 3 4) -3 (+ 5 6)))   "-2*(3+4)*(-3)*(5+6)")
  ; Products of different signs
  (check-equal? (~ '(* -2 -3)) "-2*(-3)")
  (check-equal? (~ '(* -2  3)) "-2*3")
  (check-equal? (~ '(*  2  3)) "2*3")
  (check-equal? (~ '(*  2 -3)) "2*(-3)")
  ; Special case: first factor is -1
  (parameterize ([implicit-minus-one-as-first-factor? #t]
                 [implicit-product? #f])
    (check-equal? (~ '(* -1 -3)) "-(-3)")
    (check-equal? (~ '(* -1  3)) "-3"))
  (parameterize ([implicit-minus-one-as-first-factor? #f]
                 [implicit-product? #f])
    (check-equal? (~ '(* -1 -3)) "-1*(-3)")
    (check-equal? (~ '(* -1  3)) "-1*3"))
  (parameterize ([implicit-product? #t])  
    (check-equal? (~ '(* -1 -3)) "-(-3)")
    (check-equal? (~ '(* -1  3)) "-3"))
                
  ; Explicit products
  (parameterize ([implicit-product? #f])
    (check-equal? (~ '(* 2 x)) "2*x")
    (check-equal? (~ '(*  1 x)) "x")
    (check-equal? (~ '(* -1 x)) "-x")
    (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "4*(-7-a)"))
  ; Implicit products    
  (parameterize ([implicit-product? #t])
    (check-equal? (~ '(* 2 x)) "2x")
    (check-equal? (~ '(*  1 x)) "x")
    (check-equal? (~ '(* -1 x)) "-x")
    (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "4(-7-a)"))
  (parameterize ([mode 'latex] [implicit-product? #f])
    (check-equal? (~ '(* 2 x)) "$2\\cdot x$"))
  (parameterize ([mode 'latex] [implicit-product? #t])
    (check-equal? (~ '(* 2 x)) "$2x$"))

  ;;; UNARY MINUS AKA SIGN CHANGE
  (check-equal? (~ '(- 2)) "-2")
  (check-equal? (~ '(- x)) "-x")
  (check-equal? (~ '(- (+ 1 2)))  "-(1+2)")
  (check-equal? (~ '(- (* 2 3)))  "-2*3")
  (check-equal? (~ '(- (* -2 3))) "-(-2*3)")
  (check-equal? (~ '(- (- 4)))    "-(-4)")
  ;;; SUMS WITH UNARY MINUS
  (parameterize ([use-minus-in-sums? #t])
    (check-equal? (~ '(+ a (- b) c (- d))) "a-b+c-d"))

  ;;; BINARY MINUS
  (check-equal? (~ '(- 2 3)) "2-3")
  (check-equal? (~ '(- x 3)) "x-3")
  (check-equal? (~ '(- 2 y)) "2-y")
  (check-equal? (~ '(- -3 x)) "-3-x")
  (check-equal? (~ '(- 3 -4)) "3-(-4)")
  (check-equal? (~ '(- x -4)) "x-(-4)")
  (check-equal? (~ '(- 2 (+ 3 4))) "2-(3+4)")

  (parameterize ([implicit-product? #f])
    (check-equal? (~ '(* 4 (+ -7 (* -1 a))))  "4*(-7-a)")
    (check-equal? (~ '(+ (* 3 (- x -2))))     "3*(x-(-2))")
    (check-equal? (~ '(+ (* -3 (- x -2)) -4)) "-3*(x-(-2))-4")
    (check-equal? (~ '(+ (*  3 (- x -2)) -4)) "3*(x-(-2))-4")
    (check-equal? (~ '(+ (*  3 (- x 2)) -4))  "3*(x-2)-4"))

  (parameterize ([implicit-product? #t])
    (check-equal? (~ '(* 1/2 a b c))    "1/2abc"))      ; todo: change?
  (parameterize ([mode 'latex] [implicit-product? #t])  
    (check-equal? (~ '(* 1/2 a b c))    "$\\frac{1}{2}abc$"))

  ;;; QUOTIENTS
  (check-equal? (~ '(/  2  3))     "2/3")
  (check-equal? (~ '(/  x  3))     "x/3")
  (check-equal? (~ '(/  2  y))     "2/y")
  (check-equal? (~ '(/ -3  x))     "-3/x")
  (check-equal? (~ '(/  3 -4))     "3/-4")
  (check-equal? (~ '(/  x -4))     "x/-4")
  (check-equal? (~ '(/ 2 (+ 3 4))) "2/(3+4)")

  (check-equal? (~ '(/ 2 (/ 3 4)))  "2/(3/4)")
  (check-equal? (~ '(/ (/ 2 3) 4))  "(2/3)/4")
  (check-equal? (~ '(/ (/ 2 3) (/ 4 5)))  "(2/3)/(4/5)")

  (parameterize ([mode 'latex])
    (check-equal? (~ '(*  2  3))     "$2\\cdot 3$")
    (check-equal? (~ '(/  2  3))     "$\\frac{2}{3}$"))

  ;;; SQUARE ROOTS
  (check-equal? (~ '(sqrt 2))     "sqrt(2)")
  (check-equal? (~ '(sqrt x))     "sqrt(x)")
  (check-equal? (~ '(sqrt 2/3))   "sqrt(2/3)")

  (parameterize ([mode 'latex])
    (check-equal? (~ '(sqrt 2))     "$\\sqrt{2}$")
    (check-equal? (~ '(sqrt x))     "$\\sqrt{x}$")
    (check-equal? (~ '(sqrt 2/3))   "$\\sqrt{\\frac{2}{3}}$"))

  ;;; SQUARES  
  (check-equal? (~ '(sqr  3))     "3^2")
  (check-equal? (~ '(sqr -3))     "(-3)^2")
  (check-equal? (~ '(sqr x))      "x^2")
  (check-equal? (~ '(sqr (- x)))  "(-x)^2")
  (check-equal? (~ '(sqr 2/3))    "(2/3)^2")

  (parameterize ([mode 'latex])
    (check-equal? (~ '(sqr  3))     "$3^2$")
    (check-equal? (~ '(sqr -3))     "${(-3)}^2$")
    (check-equal? (~ '(sqr x))      "$x^2$")
    (check-equal? (~ '(sqr (- x)))  "${(-x)}^2$")
    (check-equal? (~ '(sqr 2/3))    "${(\\frac{2}{3})}^2$"))
  
  ;;; ROOTS
  (parameterize ([output-root-as-power? #t])
    (check-equal? (~ '(root 2   3))   "root(2,3)")   ; cube root
    (check-equal? (~ '(root x   3))   "root(x,3)")
    (check-equal? (~ '(root 2/3 3))   "root(2/3,3)"))
  (parameterize ([output-root-as-power? #t] [use-sqrt-for-two-as-root-exponent? #t])
    (check-equal? (~ '(root 3   2))   "sqrt(3)")  
    (check-equal? (~ '(root x   2))   "sqrt(x)")
    (check-equal? (~ '(root 2/3 2))   "sqrt(2/3)"))
  (parameterize ([output-root-as-power? #t] [use-sqrt-for-two-as-root-exponent? #f])
    (check-equal? (~ '(root 3   2))   "root(3,2)")  
    (check-equal? (~ '(root x   2))   "root(x,2)")
    (check-equal? (~ '(root 2/3 2))   "root(2/3,2)"))
  (parameterize ([mode 'latex] [output-root-as-power? #t])
    (check-equal? (~ '(root 2   3)) "$\\sqrt[3]{2}$")
    (check-equal? (~ '(root x   3)) "$\\sqrt[3]{x}$")
    (check-equal? (~ '(root 2/3 3)) "$\\sqrt[3]{\\frac{2}{3}}$"))
  (parameterize ([mode 'latex] [output-root-as-power? #t] [use-sqrt-for-two-as-root-exponent? #t])
    (check-equal? (~ '(root 2   2)) "$\\sqrt{2}$")
    (check-equal? (~ '(root x   2)) "$\\sqrt{x}$")
    (check-equal? (~ '(root 2/3 2)) "$\\sqrt{\\frac{2}{3}}$"))
  (parameterize ([mode 'latex] [output-root-as-power? #t] [use-sqrt-for-two-as-root-exponent? #f])
    (check-equal? (~ '(root 2   3)) "$\\sqrt[3]{2}$")
    (check-equal? (~ '(root x   3)) "$\\sqrt[3]{x}$")
    (check-equal? (~ '(root 2/3 3)) "$\\sqrt[3]{\\frac{2}{3}}$"))

  ;;; POWERS
  (parameterize ([mode 'default])
    (check-equal? (~ '(expt x 2))          "x^2")
    (check-equal? (~ '(expt x 2/3))        "x^(2/3)")
    (check-equal? (~ '(expt x (+ 2 3)))    "x^(2+3)")
    (check-equal? (~ '(expt x (* 2 3)))    "x^(2*3)")
    (check-equal? (~ '(expt x (expt 2 3))) "x^(2^3)")
    (check-equal? (~ '(expt (expt 2 3) x)) "(2^3)^x")
    (check-equal? (~ '(expt (- x) 2))      "(-x)^2")

    (check-equal? (~ '(expt (- 1 p) (- n r))) "(1-p)^(n-r)"))

  
  (parameterize ([mode 'default] [use-quotient-for-exponent-minus-one? #t])
    (check-equal? (~ '(expt 2   -1))  "1/2")
    (check-equal? (~ '(expt x   -1))  "1/x")
    (check-equal? (~ '(expt 2/3 -1))  "1/(2/3)"))

  (parameterize ([mode 'latex])
    (check-equal? (~ '(expt x 2))  "$x^2$")
    (check-equal? (~ '(expt x 23))  "$x^{23}$"))

  ;;; DIFFERENCE
  (parameterize ([mode 'default])
    (check-equal? (~ '(/ x (- y z)))       "x/(y-z)")
    (check-equal? (~ '(/ (- y z) x))       "(y-z)/x")
    (check-equal? (~ '(/ (- y z) (+ x 1))) "(y-z)/(x+1)")
    (check-equal? (~ '(- (* 2 3) (*  4 5))) "2*3-4*5")
    (check-equal? (~ '(- (* 2 3) (* -4 5))) "2*3-(-4*5)"))
  (parameterize ([mode 'latex])
    (check-equal? (~ '(/ x (- y z)))       "$\\frac{x}{y-z}$")
    (check-equal? (~ '(/ (- y z) x))       "$\\frac{y-z}{x}$")
    (check-equal? (~ '(/ (- y z) (+ x 1))) "$\\frac{y-z}{x+1}$"))
    
  ;;; FUNCTION APPLICATION
  (parameterize ([mode 'default])
    (check-equal? (~ '(f))            "f()")
    (check-equal? (~ '(f 1))          "f(1)")
    (check-equal? (~ '(f 1 2))        "f(1,2)")
    (check-equal? (~ '(f 1 2 3))      "f(1,2,3)")
    (check-equal? (~ '(f (+ x y)))    "f(x+y)")
    (check-equal? (~ '(f (* x y)))    "f(x*y)")
    (check-equal? (~ '(f (expt x y))) "f(x^y)")
    (check-equal? (~ '(f (root x y))) "f(root(x,y))")
    (check-equal? (~ '(f (sqrt x)))   "f(sqrt(x))")
    (check-equal? (~ '(sin x))        "sin(x)"))

  (parameterize ([mode 'mma])
    (check-equal? (~ '(f))            "f[]")
    (check-equal? (~ '(f 1))          "f[1]")
    (check-equal? (~ '(f 1 2))        "f[1,2]")
    (check-equal? (~ '(f 1 2 3))      "f[1,2,3]")
    (check-equal? (~ '(f (+ x y)))    "f[x+y]")
    (check-equal? (~ '(f (* x y)))    "f[x*y]")
    (check-equal? (~ '(f (expt x y))) "f[x^y]")
    (check-equal? (~ '(f (root x y))) "f[Root[x,y]]")
    (check-equal? (~ '(f (sqrt x)))   "f[Sqrt[x]]")
    (check-equal? (~ '(Sin x))        "Sin[x]"))

  (parameterize ([mode 'latex])
    (check-equal? (~ '(f))            "$f()$")
    (check-equal? (~ '(f 1))          "$f(1)$")
    (check-equal? (~ '(f 1 2))        "$f(1,2)$")
    (check-equal? (~ '(f 1 2 3))      "$f(1,2,3)$")
    (check-equal? (~ '(f (+ x y)))    "$f(x+y)$")
    (check-equal? (~ '(f (* x y)))    "$f(x\\cdot y)$")
    (check-equal? (~ '(f (expt x y))) "$f(x^y)$")
    (check-equal? (~ '(f (root x y))) "$f(\\sqrt[y]{x})$")
    (check-equal? (~ '(f (sqrt x)))   "$f(\\sqrt{x})$")
    (check-equal? (~ '(sin x))        "$\\sin(x)$"))

  ;;; PARENS
  (parameterize ([mode 'default])
    (check-equal? (~ '(paren))       "()")
    (check-equal? (~ '(paren 1))     "(1)")
    (check-equal? (~ '(paren 1 2))   "(1,2)")
    (check-equal? (~ '(paren 1 2 3)) "(1,2,3)"))
  (parameterize ([mode 'latex])
    (check-equal? (~ '(paren))       "${\\left(\\right)}$")
    (check-equal? (~ '(paren 1))     "${\\left(1\\right)}$")
    (check-equal? (~ '(paren 1 2))   "${\\left(1,2\\right)}$")
    (check-equal? (~ '(paren 1 2 3)) "${\\left(1,2,3\\right)}$"))

  ;;; INTERVALS
  (parameterize ([mode 'default])
    (check-equal? (~ '(ccinterval 2 3)) "[2,3]")
    (check-equal? (~ '(ocinterval 2 3)) "]2,3]")
    (check-equal? (~ '(cointerval 2 3)) "[2,3[")
    (check-equal? (~ '(oointerval 2 3)) "]2,3["))

  ;;; DIFFERENTIATION
  (parameterize ([mode 'default] [output-differentiation-mark '(x)])
    (check-equal? (~ '(diff f))          "f'")
    (check-equal? (~ '(diff (f x) x))    "f'(x)")
    ; (check-equal? (~ '(diff (f x) y))    "f'(x)")
    (check-equal? (~ '(diff (sqrt x) x)) "(sqrt(x))'"))

  (parameterize ([mode 'latex] [output-differentiation-mark '(x)])
    (check-equal? (~ '(diff f))          "$f'$")
    (check-equal? (~ '(diff (f x) x))    "$f'(x)$")
    (check-equal? (~ '(diff (f x) y))    "$\\dv{y}(f(x))$")
    (check-equal? (~ '(diff (sqrt x) x)) "$(\\sqrt{x})'$"))



  ;;; -------------------      
  ;;; Old Tests
  ;;; -------------------      
  
  (check-equal? (~ '(* -1 x)) "-x")
  (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "4*(-7-a)")
  (check-equal? (~ '(+ (* -3 (- x -2)) -4)) "-3*(x-(-2))-4")
  (check-equal? (~ '(+ (*  3 (- x -2)) -4)) "3*(x-(-2))-4")
  (check-equal? (~ '(+ (*  3 (- x 2)) -4)) "3*(x-2)-4")
  (check-equal? (~ `(+ (expt 2 3) (* 5 2) -3)) "2^3+5*2-3")
  (check-equal? (~ '(+ (expt -1 2) (* 3 -1) -2)) "(-1)^2+3*(-1)-2")
  (check-equal? (~ '(+ 1 -2 3)) "1-2+3")
  (check-equal? (~ '(+ 1 (* -2 x) 3)) "1-2*x+3")
  (check-equal? (parameterize ([use-sqrt-for-half-as-exponent? #f])
                  (~ '(expt x 1/2))) "x^(1/2)")
  (check-equal? (parameterize ([use-sqrt-for-half-as-exponent? #t])
                  (~ '(expt x 1/2))) "sqrt(x)")
  (check-equal? (~ '(+ 1 (* 7 (expt x -1)))) "1+7/x")
  ; (check-equal? (~ '(formatting ([use-quotients? #f]) (+ 1 (* 7 (expt x -1))))) "1+7*1/x")
  ; (check-equal? (~ '(formatting ([use-quotients? #t]) (+ 1 (* 7 (expt x -1))))) "1+7/x")
  (check-equal? (~ '(expt (expt 65 1/2) 2)) "sqrt(65)^2")
  (check-equal? (~ '(+ 1 (* 2 a b) 1)) "1+2*a*b+1")
  (check-equal? (~ '(+ (* 2 y) (* -1 (+ 2 x)))) "2*y-(2+x)")
  (check-equal? (~ '(+ (* -1 (+ y 1)) 3)) "-(y+1)+3")
  (check-equal? (~ '(* (+ 1 x) -2 (+ 3 x))) "(1+x)*(-2)*(3+x)")
  (check-equal? (~ '(* (+ 1 x)  2 (+ 3 x))) "(1+x)*2*(3+x)")
  (check-equal? (~ '(* (+ 1 x)  z (+ 3 x))) "(1+x)*z*(3+x)")
  (check-equal? (~ '(* (+ 1 x) (+ 2 y) (+ 3 x))) "(1+x)*(2+y)*(3+x)")
  (check-equal? (~ '(+ (* (+ 1 x) (+ 2 x) (+ 3 x))
                       (* (+ 1 x) (+ 2 x) (+ 4 x))
                       (* (+ 1 x) (+ 3 x) (+ 4 x))
                       (* (+ 2 x) (+ 3 x) (+ 4 x)))) 
                "(1+x)*(2+x)*(3+x)+(1+x)*(2+x)*(4+x)+(1+x)*(3+x)*(4+x)+(2+x)*(3+x)*(4+x)")
  (check-equal? (~ '(expt (/ a b)  2)) "(a/b)^2")
  (parameterize ([use-quotient-for-negative-exponent? #f] [use-quotient? #f])
    (check-equal? (~ '(expt (/ a b) -2)) "(a/b)^(-2)")
    (check-equal? (~ '(expt a -2)) "a^(-2)")
    (check-equal? (~ '(expt  2 (expt   3  4))) "2^(3^4)")
    (check-equal? (~ '(expt -2 (expt  -3  4))) "(-2)^((-3)^4)")
    (check-equal? (~ '(expt -2 (expt  -3 -4))) "(-2)^((-3)^(-4))"))
    
  (check-equal? (~ '(expt (* (expt a 2) (expt b 3)) 4))
                "(a^2*b^3)^4")


  (check-equal? (~ '(- (- x 3))) "-(x-3)")
  ;; (parameterize ([output-implicit-product? #t])
  ;;   (check-equal? (~ (expand (Expt (⊕ x 1) 3)))
  ;;                 "1+3x+3x^2+x^3"))
  (check-equal? (~ '(sin (+ x -7))) "sin(x-7)")
  (check-equal? (~ '(* (sin (+ x -7)) (+ (cos (+ x -7)) (asin (+ x -7)))))
                "sin(x-7)*(cos(x-7)+asin(x-7))")
  ;; (check-equal? (parameterize ([bf-precision 100]) (verbose~ pi.bf))
  ;;               "3.1415926535897932384626433832793")

  ; --- MMA
  (parameterize ([mode 'mma])
    (check-equal? (~ '(sin (+ x -7))) "Sin[x-7]"))
  (parameterize ([mode 'default])
    (check-equal? (~ '(sin (+ x -7))) "sin(x-7)")
    (check-equal? (~ '(* -1 x)) "-x")
    (check-equal? (~ '(+ (* -1 x) 3)) "-x+3")
    (check-equal? (~ '(+ (expt x 2) (* -1 x) 3)) "x^2-x+3")
    (check-equal? (~ '(/ x (- 1 (expt y 2)))) "x/(1-y^2)")
    (check-equal? (~ '(* 2 x y)) "2*x*y"))

  ; --- LATEX
  (parameterize ([mode 'latex] [implicit-product? #t])
    (check-equal? (~ 4)   "$4$")
    (check-equal? (~ 2/3) "$\\frac{2}{3}$")

    
    (check-equal? (~ '(/ x (- 1 (expt y 2)))) "$\\frac{x}{1-y^2}$")
    (check-equal? (~ '(* -8 x )) "$-8x$")
    (check-equal? (~ '(- 1 (+ 2 3))) "$1-(2+3)$")
    (check-equal? (~ '(* -1 (expt (- x 1) 2))) "$-(x-1)^2$")


    (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "$4(-7-a)$")
    (check-equal? (~ '(* 3 6)) "$3\\cdot 6$")
    (check-equal? (~ '(sqrt d)) "$\\sqrt{d}$")
    (check-equal? (~ '(* (sqrt d) a)) "$\\sqrt{d}\\cdot a$")
    (check-equal? (~ '(* -4 (expt -1 3))) "$-4\\cdot {(-1)}^3$")

    (check-equal? (~ '(* -9 (expt x -10))) "$\\frac{-9}{x^{10}}$")
    (check-equal? (~ '(- (* 2 3) (* -1  4))) "$2\\cdot 3-(-4)$")      ; XXX
    (check-equal? (~ '(- (* 2 3) (* -1 -4))) "$2\\cdot 3-(-(-4))$")
    (check-equal? (~ '(* -1 (* (- x 1) (- x 2)))) "$-(x-1)\\cdot (x-2)$") ; YYY


    (check-equal? (~ '(paren -3)) "${\\left(-3\\right)}$")
    (check-equal? (~ '(red  (paren -3))) "${\\color{red}{\\left(-3\\right)}\\color{black}}$")
    (check-equal? (~ '(blue (paren -3))) "${\\color{blue}{\\left(-3\\right)}\\color{black}}$")
    (check-equal? (~ '(green  (paren -3))) "${\\color{green}{\\left(-3\\right)}\\color{black}}$")
    (check-equal? (~ '(purple (paren -3))) "${\\color{purple}{\\left(-3\\right)}\\color{black}}$")
    (check-equal? (~ '(paren x_1 y_1))   "${\\left(x_1,y_1\\right)}$")
    (check-equal? (~ '(~ X (bi n p)))    "$X \\approx \\text{bi}(n,p)$")


    (check-equal? (~ '(* 1/2 1/3))              "$\\frac{1}{2}\\cdot \\frac{1}{3}$")
    (check-equal? (~ '(sqrt (* 1/2 1/3)))       "$\\sqrt{{\\frac{1}{2}\\cdot \\frac{1}{3}}}$")
    (check-equal? (~ '(sqrt (* 12 1/12 11/12))) "$\\sqrt{{12\\cdot \\frac{1}{12}\\cdot \\frac{11}{12}}}$")

    (parameterize ([output-root? #t])
      (check-equal? (~ '(expt 2 1/3)) "$\\sqrt[3]{2}$"))

    (check-equal? (~ '(- (sqr c) (sqr a))) "$c^2-a^2$")

    (check-equal? (~ '(Less         x 1)) "$x < 1$")
    (check-equal? (~ '(LessEqual    x 1)) "$x ≤ 1$")
    (check-equal? (~ '(Greater      x 1)) "$x > 1$")
    (check-equal? (~ '(GreaterEqual x 1)) "$x ≥ 1$")

    (check-equal? (~ '(bar x))            "${\\bar{x}}$")
    (check-equal? (~ '(braces 1 2 3))     "${\\left\\{1,2,3\\right\\}}$")
    (check-equal? (~ '(bracket 1 2 3))    "${\\left[1,2,3\\right]}$")

    ;; Names
    (check-equal? (~ 'a)                     "$a$")
    (check-equal? (~ 'ab)                    "$\\mathrm{ab}$")
    (check-equal? (~ 'a_1)                   "$a_1$")
    (check-equal? (~ 'ab_1)                  "$\\mathrm{ab}_1$")
    (check-equal? (~ 'h_a)                   "$h_a$")
    (check-equal? (~ 'mellemliggende-vinkel) "$\\mathrm{mellemliggende\\;vinkel}$")
    (check-equal? (~ '(= T (* 1/2 a b (sin C))))  "$T = \\frac{1}{2}ab\\cdot \\sin(C)$")
    (check-equal? (~ '(* 1/2 a b c))              "$\\frac{1}{2}abc$")

    (check-equal? (parameterize ([implicit-product? #t]) (~ '(* 5 (sqrt 5))))
                  "$5\\sqrt{5}$")
    (check-equal? (parameterize ([implicit-product? #f]) (~ '(* 5 (sqrt 5))))
                  "$5\\cdot \\sqrt{5}$")
    (check-equal? (~ '(= (sin A) (/ (* 5 (sqrt 5)) 2))) "$\\sin(A) = \\frac{5\\sqrt{5}}{2}$")

    (parameterize ([use-quotient-for-negative-exponent? #f] [use-quotient? #f])
      (check-equal? (~ `(expt 2 -1)) "$2^{-1}$") ; a^-1 is a special case
      (check-equal? (~ `(expt 2 -3)) "$2^{-3}$") ; a^p, p negative
      (check-equal? (~ `(expt 2 -1)) "$2^{-1}$")
      (check-equal? (~ `(expt 2 -2)) "$2^{-2}$")
      (check-equal? (~ '(expt y -4)) "$y^{-4}$"))
    (check-equal? (~ '(expt 2 1)) "$2^1$")
    ;;; END LATEX
    )

  ;;; LATEX ONLY ENVIRONMENTS
  ;;; SPLIT
  #;(parameterize ([mode 'latex])
    (define (split . xs) (format-split-relation '(original) `(split ,@xs)))
    ;; The split environment supports a single alignment marker & per line.
    ;; The linebreak \\ can't occur as the last token.
    (check-equal? (split '(= a   b))           "a = b")
    (check-equal? (split '(= a   b  c))        "a = b = c")
    (check-equal? (split '(= a & b))           "a &= b")
    (check-equal? (split '(= a & b   c))       "a &= b = c")
    (check-equal? (split '(= a & b & c))       "a &= b &= c")

    (check-equal? (split '(= a \\  b))         "a\\\\ = b")
    (check-equal? (split '(= a \\  b    c))    "a\\\\ = b = c")
    (check-equal? (split '(= a \\  b \\ c))    "a\\\\ = b\\\\ = c")
    (check-equal? (split '(= a \\ & b))        "a\\\\ &= b")
    (check-equal? (split '(= a \\ & b))        "a\\\\ &= b")
    (check-equal? (split '(= a \\ & b      c)) "a\\\\ &= b = c")
    (check-equal? (split '(= a \\ & b \\ & c)) "a\\\\ &= b\\\\ &= c"))
  )

