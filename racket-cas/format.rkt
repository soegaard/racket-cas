#lang racket/base
(provide (all-defined-out))

(require racket/format racket/list racket/match racket/math racket/string 
         math/bigfloat
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "normalize.rkt" "up-ref.rkt" "compose-app.rkt"
         "logical-operators.rkt" "relational-operators.rkt" "expand.rkt" "trig.rkt"
         "parameters.rkt"
         (prefix-in % "bfracket.rkt"))

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))

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
  (match x ['@pi "π"]  ['@i "i"] ['@e "\\mathrm{e}"] 
         [(? symbol? x)
          (define s (symbol->string x))
          (cond
            ; single letter variables are italic
            [(= (string-length s) 1)  (symbol->tex x)]
            ; identifiers with subscripts
            [(string-contains? s "_")
             (define parts           (string-split s "_"))
             (define formatted-parts (map tex-output-variable-name (map string->symbol parts)))
             (string-append* (add-between (map ~a formatted-parts) "_"))]
            [(string-contains? s "-")
             ; An dash in an identifer is formatted as a space
             (~a "\\mathrm{" (symbol->tex (string->symbol (string-replace s "-" "\\;"))) "}")]
            [else
             (~a "\\mathrm{" (symbol->tex x) "}")])]))

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


;;; Intervals
(define (default-output-interval u)
  (define v~ verbose~)
  (parameterize ([output-wrapper values]) ; avoid $ around sub parts
    ; (displayln (list 'default-output-interval u))
    (match u
      [(list 'ccinterval -inf.0 +inf.0) (~a "]" "-∞"   ","  "∞"   "[")]
      [(list 'ocinterval -inf.0      v) (~a "]" "-∞"   "," (v~ v) "]")]
      [(list 'cointerval u      +inf.0) (~a "[" (v~ u) "," "∞"    "[")]
      
      [(list 'ccinterval u v) (~a "[" (v~ u) "," (v~ v) "]")]
      [(list 'ocinterval u v) (~a "]" (v~ u) "," (v~ v) "]")]
      [(list 'cointerval u v) (~a "[" (v~ u) "," (v~ v) "[")]
      [(list 'oointerval u v) (~a "]" (v~ u) "," (v~ v) "[")]
      [_ (error 'default-output-interval (~a "unknown interval type, got: " u))])))
  
(define (tex-output-interval u)
  ; (displayln (list 'tex-output-interval u))
  (define v~ verbose~)
  (parameterize ([output-wrapper values]) ; avoid $ around sub parts
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
      [_ (error 'tex-output-interval (~a "unknown interval type, got: " u))])))

;;; Formatting Parameters

(define output-mode                      (make-parameter #f)) ; #f=default, 'default, 'mma or 'tex 
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
(define output-format-negative-exponent  (make-parameter #f))  ; use 1/2 or 2^-1 to output negative exponents
(define output-terms-descending?         (make-parameter #f)) ; reverse terms before outputting?
(define output-implicit-product?         (make-parameter #f)) ; useful for TeX
(define output-relational-operator       (make-parameter ~a)) ; useful for TeX
(define output-floating-point-precision  (make-parameter 4))  ; 
(define output-variable-name             (make-parameter default-output-variable-name)) ; also handles @e, @pi and @i
(define output-differentiation-mark      (make-parameter '(x))) ; use (u)' rather than d/dx(u) for variables in this list
(define output-fraction                  (make-parameter default-output-fraction))
(define output-interval                  (make-parameter default-output-interval))

(define (use-mma-output-style)
  (output-mode 'mma)
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
  (output-format-negative-exponent #f)
  (output-implicit-product? #f)
  (output-relational-operator ~a)
  (output-variable-name mma-output-variable-name)
  (output-fraction mma-output-fraction))

(define (use-default-output-style)
  (output-mode 'default)
  (output-application-brackets (list "(" ")"))
  (output-format-function-symbol ~a)
  (output-format-quotient #f)
  (output-format-quotient-parens (list "(" ")"))
  (output-sub-expression-parens  (list "(" ")"))
  (output-sub-exponent-parens    (list "(" ")"))
  (output-sub-exponent-wrapper   values)
  (output-format-negative-exponent #f)
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
  (output-mode 'tex)
  (define operators '(sin cos tan log ln sqrt det))
  (define (~relop u)
    (match u
      ['<=           "≤ "]
      ['>=           "≥ "]
      ['≤            "≤ "]
      ['≥            "≥ "]
      ['~            "\\approx "]
      ['Less         "< "]      
      ['LessEqual    "≤ "]
      ['Greater      "> "]
      ['GreaterEqual "≥ "]
      [_    (~a u)]))
  (define (~symbol s) 
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
      [_  (define t (~a s))
          (if (= (string-length t) 1) t (~a "\\text{" t "}"))]))
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
  (output-format-negative-exponent #f)
  (output-implicit-product? #t)
  (output-relational-operator ~relop)
  (output-variable-name tex-output-variable-name)
  (output-fraction tex-output-fraction)
  (output-interval tex-output-interval))

(define (tex u)
  (define operators '(sin  cos  tan log ln sqrt
                           det
                      sinh cosh tanh )) ; needs \\ in output
  (define relational-operators '(= < <= > >=))
  (define (~relop u)
    (match u
      ['<=  "≤ "]
      ['>=  "≥ "]
      ['~   "\\approx "]
      ['Less         "< "]
      ['LessEqual    "≤ "]
      ['Greater      "> "]
      ['GreaterEqual "≥ "]
      [_    (~a u)]))
  (define (~symbol s)
    (match s
      ['acos "\\cos^{-1}"]
      ['asin "\\sin^{-1}"]
      ['atan "\\tan^{-1}"]
      [_ #:when (member s operators) (~a "\\" s)]      
      ['<=  "\\leq "]
      ['>=  "\\geq "]
      ['~   "\\approx "]
      ['*   "\\cdot "]   ; multiplication
      ['or  "\\vee "]    ; logical or
      ['and "\\wedge "]  ; logical and
      ['|%| "\\%"]
      [_  (define t (~a s))
          (if (= (string-length t) 1) t (~a "\\text{" t "}"))]))
  (parameterize ((output-mode 'tex)
                 (output-application-brackets (list "(" ")"))
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
                 ; (output-format-negative-exponent #f) ; omitted on purpose
                 (output-implicit-product?    (default-output-implicit-product?)) ; #t
                 (output-relational-operator  ~relop)
                 (output-variable-name        tex-output-variable-name)
                 (output-format-log           tex-output-log)
                 (output-format-up            tex-output-up)
                 (output-fraction             tex-output-fraction)
                 (output-interval             tex-output-interval))
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
         #:zero-term   [zero-term   #f]  ; #t means: remove  0 in sums
         #:one-factor  [one-factor  #f]  ; #t means: rewrite (* 1 u) to u
         #:zero-factor [zero-factor #f]  ; #t means: rewrite (* 0 u) to 0
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
                        [(list 0 0) #:when zero-term 0]
                        [(list 0 u) #:when zero-term u]
                        [(list u 0) #:when zero-term u]
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
     [_ ; (display u)
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
  ; (displayln (list 'verbose~ u))
  (match-define (list app-left  app-right)  (output-application-brackets))
  (match-define (list sub-left  sub-right)  (output-sub-expression-parens))
  (match-define (list expt-left expt-right) (output-sub-exponent-parens))
  (match-define (list quot-left quot-right) (output-format-quotient-parens))
  ;(define use-quotients? (output-use-quotients?))
  (define ~sym (let ([sym (output-format-function-symbol)]) (λ (x) (sym x)))) ; function names
  (define ~var (let ([out (output-variable-name)]) (λ(x) (out x)))) ; variable names
  (define (~relop x) ((output-relational-operator) x))
  (define (~red str)    (~a "{\\color{red}"    str "\\color{black}}"))
  (define (~blue str)   (~a "{\\color{blue}"   str "\\color{black}}"))
  (define (~green str)  (~a "{\\color{green}"  str "\\color{black}}"))
  (define (~purple str) (~a "{\\color{purple}" str "\\color{black}}"))
  (define (~explicit-paren strs)
    (case (output-mode)
      [(tex) (~a "{\\left(" (string-append* (add-between strs ",")) "\\right)}")]
      [else  (~a        "(" (string-append* (add-between strs ",")) ")")]))  
  (define (v~ u [original? #f])
    ; (displayln (list 'v~ u 'orig original?))
    (define ~frac (output-fraction))
    (define (~num r)
      (define precision (output-floating-point-precision))
      (cond [(eqv? r -inf.0) "-∞"]
            [(eqv? r +inf.0) "∞"]
            [(and (exact? r) (> (denominator r) 1)) (~frac r)]
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
      (define (non-integer-fraction? u)
        (and (number? u) (exact? u) (> (denominator u) 1)))
      (if (and (number? u) (or (negative? u) (non-integer-fraction? u)))
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
      ; (displayln (list 'implicit* u v))
      (cond
        [(output-implicit-product?)
         (math-match u
           ; first factor is a number          
           [r (math-match v
                [s                    (~sym '*)]
                [x                     implicit-mult]
                [(⊗ u1 u2)            (implicit* r u1)]
                [(Expt u1 u2)         (implicit* r u1)]
                [(list '+ u1 u2 ...)   implicit-mult]
                [(list 'vec u1 u2 ...) implicit-mult]  
                [(list 'sqrt u1)       implicit-mult]
                [(list 'sqr u1)        implicit-mult]
                [(list 'up _ ...)      implicit-mult]
                [_                   (~sym '*)])]
           ; first factor is a symbol
           [x (define s (~a x))
              (if (or (= (string-length s) 1)
                      (and (string-contains? s "_")
                           (>= (string-length s) 2)
                           (eqv? (string-ref s 1) #\_)))
                  ; only single letter variables (possibly with an index) uses implicit 
                  (math-match v
                    [s                    (~sym '*)]
                    [y                     implicit-mult]
                    [(⊗ u1 u2)            (implicit* x u1)]
                    [(Expt u1 u2)         (implicit* x u1)]
                    [(list '+ u1 u2 ...)   implicit-mult]
                    [(list 'vec u1 u2 ...) implicit-mult]  
                    [(list 'sqrt u1)       implicit-mult]
                    [(list 'sqr  u1)       implicit-mult]
                    [(list 'up _ ...)      implicit-mult]
                    [_                   (~sym '*)])
                  ; other variables uses explicit
                  (~sym '*))]
           ; anything else is explicit
           [_ (~sym '*)])]
        ; if implicit products are off, always use *
        [else (~sym '*)]))

    (define (prefix-minus s)
      (if (eqv? (string-ref s 0) #\-)
          (~a "-(" s ")")
          (~a "-" s)))
             
    (define (par u
                 #:use             [wrap paren]
                 #:wrap-fractions? [wrap-fractions? #f]
                 #:exponent-base?  [exponent-base? #f]) ; wrap if (locally) necessary
      (when debugging? (displayln (list 'par u 'orig original? 'exponent-base exponent-base?)))
      (math-match u
        [(list 'red    u) (~red    (par u))]           ; red   color
        [(list 'blue   u) (~blue   (par u))]           ; blue  color
        [(list 'green  u) (~green  (par u))]           ; green color
        [(list 'purple u) (~purple (par u))]           ; purpe color
        [(list 'paren u ...) (~explicit-paren (map v~ u))] ; explicit parens (tex)
        [α    #:when (and wrap-fractions? (not (integer? α))) (wrap (~frac α))] ; XXX
        [α    #:when (and (not (integer? α)) exponent-base?)  (wrap (~frac α))] ; XXX
        [α    #:when (not (integer? α))                             (~frac α)] ; XXX
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

        [(⊗ u v) #:when exponent-base?   (exponent-wrap (paren (~a (par u) (~sym '*) (par v))))] ; TODO XXX ~ two layers
        [(⊗ r u) #:when (positive? r)   (~a           (~num (abs r)) (implicit* r u) (par u))] ; XXX YY
        [(⊗ u v) #:when original?         (let ([s (~a (par u)  (implicit* u v) (par v))])
                                           s)] ; XXX
        [(⊗ u v)                       (~a (par u) (implicit* u v) (par v))] ; YYY
        [(⊕ _ __)    (wrap u)]
        [(list* '- _ __) (wrap u)]
        [(And u v)   (~a (par u) " " (~sym 'and) " " (par v))]
        [(Or u v)    (~a (par u) " " (~sym 'or)  " " (par v))]
        [(Equal u v) (~a (par u) " " (~sym '=)   " " (par v))]
        ; powers
        [(Expt u 1/2) #:when (output-sqrt?) ((output-format-sqrt) u)]
        [(Expt u -1)    (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                        (cond [(output-format-negative-exponent) (~a (par u) "^" (exponent-wrap -1))]
                              [else                              (format/ 1 (par u #:use quotient-sub))])]
        ; unnormalized power of a power
        [(Expt (and (Expt u v) w) w1) (~a ((output-sub-exponent-wrapper) ; braces for tex otherwise nothing
                                           (v~ w)) 
                                          (~sym '^) ((output-sub-exponent-wrapper)
                                                     (fluid-let ([original? #t])
                                                       (par v #:use exponent-sub
                                                            #:wrap-fractions? #t))))]
        [(Expt u p)   (if (and (negative? p) (output-format-negative-exponent))
                          ; note: LaTeX needs to wrap the base in {} if u is an exponent
                          (~a ((output-sub-exponent-wrapper) (par u)) "^" (exponent-wrap p)) 
                          (~a (par u #:use base-sub #:exponent-base? #t)
                              (~sym '^) ((output-sub-exponent-wrapper)
                                         (fluid-let ([original? #t])
                                                    (par p #:use exponent-sub)))))]
        [(Expt u α)   #:when (= (numerator α) -1) ; -1/p
                        (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                        (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub))]
        [(Expt u v)   (~a (par u #:use base-sub #:exponent-base? #t)
                          (~sym '^) ((output-sub-exponent-wrapper)
                                     (fluid-let ([original? #t])
                                        (par v #:use exponent-sub #:wrap-fractions? #t))))]
        [(Log u)      ((output-format-log) u)]
        [(Log u v)    ((output-format-log) u v)]
        [(Up u v)     ((output-format-up)  u v)]
        
        [(app: f us) #:when (memq f '(< > <= >=))
                     (match us [(list u v) (~a (v~ u) (~relop f) (v~ v))])]
        ; unnormalized quotient
        [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                       (define out     (format/ (par u #:use quotient-sub) (par v #:use quotient-sub)))
                       (if exponent-base? (base-sub out) out)]
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
        [(list 'diff (list 'vecfun u) x)
         #:when (member x (output-differentiation-mark))
         (~a "\\vec{" (v~ u) "}^{\\prime}" "(" (v~ x) ")" )]
        [(list 'diff f)
         #:when (symbol? f)                              (~a (~sym f) "'")]
        [(list 'diff (list f x) x)
         #:when (and (symbol? f) (symbol? x))            (~a (~sym f) "'(" (~var x) ")")]
        [(list 'diff (list f x) x u) ; f'(x)|x=x0 i.e.  f'(x0)
         #:when (and (symbol? f) (symbol? x))   (~a (~sym f) "'(" (v~ u) ")")]
        [(list 'diff u x)
         #:when (and (symbol? u) (member x (output-differentiation-mark))) (~a (v~ u #t) "' ")]
        [(list 'diff u x)
         #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
        [(list 'diff u  x)                               (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]

        [(list 'percent u) (~a (v~ u) (~sym '|%|))]
        [(list 'abs u) ((output-format-abs) u)] 
        [(list 'vec u)      (~a "\\overrightarrow{" (v~ u) "}")]               ; TODO: only for TeX 
        [(list 'vecfun u v) (~a "\\overrightarrow{" (v~ u) "}" "(" (v~ v) ")" )] ; TODO: only for TeX 
        [(list 'deg u) (~a (v~ u) "° ")]                    ; TODO: only for TeX 
        [(list 'hat u) (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX 
        [(list 'bar u) (~a "\\bar{" (v~ u) "}")]            ; TODO: only for TeX 
        [(list* 'braces  us) (apply ~a (append (list "\\{") (add-between (map v~ us) ",") (list "\\}")))] ; TODO: only for TeX 
        [(list* 'bracket us) (apply ~a (append (list   "[") (add-between (map v~ us) ",") (list "]")))] ; TODO: only for TeX 
        [(list 'int u v)   (~a "\\int " (v~ u) "\\ \\textrm{d}" (v~ v))] ; TODO: only for TeX

        ; applications
        [(app: f us) (let ()
                       (define arguments
                         (string-append* (add-between (map v~ us) ",")))
                       (define head ((output-format-function-symbol) f))
                       (~a head app-left arguments app-right))]
        [_  (wrap u)]))
    (define (t1~ u) ; term 1 aka first term in a sum
      (when debugging? (displayln (list 't1 u)))
      (math-match u
                  [(list 'red    u) (~red    (t1~ u))]
                  [(list 'blue   u) (~blue   (t1~ u))]           ; blue color
                  [(list 'green  u) (~green  (t1~ u))]
                  [(list 'purple u) (~purple (t1~ u))]  
                  [(list 'paren u ...) (~explicit-paren (map t1~ u))] ; explicit parens (tex)

                  ; unnormalized and normalized quotients
                  [(list '/ u v) (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                                 (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
                  [(Quotient u v) #:when (and  (output-use-quotients?) (not (rational? v)))
                                  (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                                  (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
                  [(⊗  1 u)                       (~a                          (v~ u))]
                  [(⊗ -1 u)                       (prefix-minus (par u))]
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
      [(list 'red    u) (~red    (v~ u))]
      [(list 'blue   u) (~blue   (v~ u))]           ; blue color
      [(list 'green  u) (~green  (v~ u))]
      [(list 'purple u) (~purple (v~ u))]
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
      [(Quotient u v) #:when (and (output-use-quotients?) (not (rational? v)))
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ (par u #:use quotient-sub) (par v #:use quotient-sub))]
      [(Expt u -1)    (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (cond [(output-format-negative-exponent)
                             (~a ((output-sub-exponent-wrapper) (par u)) "^" (exponent-wrap -1))]
                            [else (format/ 1 (par u #:use quotient-sub))])]
      [(Expt u p)     #:when (negative? p)
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (cond [(and (output-format-negative-exponent) (output-use-quotients?))
                             ; note: the base needs to be wrapped - TeX requires {} around the base to avoid
                             ;       doubles superscripts as in a^2^3
                             (~a ((output-sub-exponent-wrapper) (par u)) "^" (exponent-wrap p))]
                            [(output-use-quotients?)
                             (format/ 1 (par (Expt u (- p)) #:use quotient-sub #:exponent-base? #t))]
                            [else 
                             (~a ((output-sub-exponent-wrapper) (par u #:exponent-base? #t)) "^" (exponent-wrap p))])]
      [(Expt u α)     #:when (and (output-root?) (= (numerator α) 1) (> (abs (denominator α)) 1)
                                  ((output-format-root) u (/ 1 α))) ; α=1/n
                      ((output-format-root) u (/ 1 α))] ; only used, if (output-format-root) returns non-#f 
      [(Expt u α)     #:when (= (numerator α) -1) ; -1/p
                      (define format/  (or (output-format-quotient) (λ (u v) (~a u "/" v))))
                      (format/ 1 (par (Root u (/ 1 (- α))) #:use quotient-sub #:exponent-base? #t))]
      
      ; mult
      [(⊗  1 v)                                               (~a             (v~ v))]
      [(⊗ -1 α) #:when (negative? α)                          (~a "-" (paren  (v~ α)))]
      [(⊗ -1 α)                                               (~a "-"         (v~ α))]
      [(⊗ -1 x)                                               (~a "-"         (v~ x))]
      [(⊗ -1 (Expt  u v))                                     (~a "-" (v~ `(expt ,u ,v)))]
      [(⊗ -1 (⊗     u v)) #:when (not (equal? v '(*)))        (~a "-" (v~ `(*    ,u ,v)))] ; ex: (verbose~ '(* -1 4))
      [(⊗ -1 v)                                               (~a "-" (paren  (v~ v)))]
      [(⊗ -1 p v) #:when (and original? (negative? p))        ; (displayln (list "A" p v (⊗ p v)))
                                                              (~a "-" (paren  (v~ (⊗ p v) #f)))] ; wrong
      [(⊗ -1 v)   #:when      original?                       (~a "-"         (v~ v))]
      ; [(⊗ -1 p v) #:when                (negative? p)         (~a "-" (paren  (v~ (⊗ p v) #f)))]                 ; wrong
      [(⊗ -1 v)                                        (paren (~a "-"         (v~ v)))]
      ; Explicit multiplication between integers
      [(⊗ p q) #:when original?           (~a     (~num p)     (~sym '*) (par q))]
      [(⊗ p q) #:when (not (negative? p)) (~a     (~num p)     (~sym '*) (par q))]
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
                      ;(displayln 'X1)
                      (~a "-" (~num (abs r)) (implicit* r u) (v~ (argcons '* u v)))]
      [(⊗ r (⊗ u v))  #:when (and (positive? r) (not (equal? '(*) v)))
                      ;(displayln (list 'X2 r u v (argcons '* u v) (fluid-let ([original? #t]) (v~ (argcons '* u v) #t))))
                      (~a    (~num (abs r))  (implicit* r u) (fluid-let ([original? #t]) (v~ (argcons '* u v) #t)))] ; XXX
      [(⊗ r v)        #:when (negative? r)
                      ; (displayln 'X3)
                      (define w (if original? values paren))
                      (~a  (w (~a "-" (~num (abs r)))) (implicit* r v) (par v #:use paren))] ; XXX
      [(⊗ r v)        #:when (positive? r)
                      ;(displayln 'X4)
                      (~a     (~num r) (implicit* r v) (par v #:use paren))] ; XXX
      
      [(⊗ u v)  #:when (not (equal? '(*) v))
                ; (displayln (list 'X5 u v (par u) (fluid-let ([original? #t]) (par v))))
                (~a (par u) (implicit* u v) (fluid-let ([original? #t]) (par v)))]
      ; plus
      [(⊕ u r)              (if (negative? r)
                                (~a (t1~ u)  (~sym '-) (~num (abs r)))
                                (~a (t1~ u)  (~sym '+) (~num (abs r))))]
      [(⊕ u (⊗ -1 v))        (~a (t1~ u)  (~sym '-) (par v))] ; YYY
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
      [(⊕ u (⊕ (⊗ -1 v) w)) (~a (t1~ u)  (~sym '-) (v~ (argcons '+ (par v) w)))] ; YYY
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
       (~a (v~ u) " " (~relop '<) " " (v~ v) " " (~relop '<) " " (v~ v1))]
      [(And (LessEqual u v) (Less u1 v1))      #:when (equal? v u1)
       (~a (v~ u ) " " (~relop '<=) " " (v~ v) " " (~relop '<) " " (v~ v1))]
      [(And (LessEqual u v) (LessEqual u1 v1)) #:when (equal? v u1)
       (~a (v~ u) " " (~relop '<=) " " (v~ v) " " (~relop '<=) " " (v~ v1))]
      [(And (Less u v)      (LessEqual u1 v1)) #:when (equal? v u1)
       (~a (v~ u) " " (~relop '<)  " " (v~ v) " " (~relop '<=) " " (v~ v1))]
      
      [(And u v)            (~a (par u) " " (~sym 'and) " " (par v))]
      ; todo: if u or v contains And or Or in u or v then we need parentheses as in the And line
      [(Or u v)             (~a (v~ u) " " (~sym 'or) " " (v~ v))]      
      [(list  '= v) (~a (~sym '=) (v~ v))]
      [(list* '= us) ; handle illegal = with multiple terms
       (string-append* (add-between (map (λ (u) (v~ u #t)) us) (~a " " (~relop '=) " ")))]
      [(list* '⇔ us) ; handle ⇔ with multiple terms
       (string-append* (add-between (map (λ (u) (v~ u #t)) us) "\\ \\  \\Leftrightarrow \\ \\ "))]
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
      [(Expt u v)  (~a (par u #:exponent-base? #t #:wrap-fractions? #t) (~sym '^)
                       (fluid-let ([original? #t])
                                  ((output-sub-exponent-wrapper)
                                   (par v #:use exponent-sub
                                        #:wrap-fractions? #t))))]
      [(App u  v)   (match u
                      [(? symbol? f)             (~a          f     "(" (v~ v) ")")]
                      [(list 'vec (? symbol? f)) (~a "\\vec{" f "}" "(" (v~ v) ")")]
                      [_ (error '~v 
                                "the first subform of App is restricted to f and (vec f) in format")])]
      ; Unnormalized
      [(list 'sqr u)   (v~ `(expt ,u 2))]
      [(list 'in u v)  (~a (v~ u) "\\in " (v~ v))]
      
      ;   handle sqrt first
      [(list 'diff (list 'sqrt u) x)
       #:when (member x (output-differentiation-mark))
       (~a "(" ((output-format-sqrt) u) ")'")]      
      [(list 'diff f)
       #:when (symbol? f)                     (~a (~sym f) "'")]
      [(list 'diff (list 'vecfun u x))
       #:when (member x (output-differentiation-mark))
       (~a "\\vec{" (v~ u) "}^{\\prime}" "(" (v~ x) ")" )]
      [(list 'diff (list f x) x)
       #:when (and (symbol? f) (symbol? x))   (~a (~sym f) "'(" (~var x) ")")]
      [(list 'diff (list f x) x u) ; f'(x)|x=u i.e.  f'(u)
       #:when (and (symbol? f) (symbol? x))   (~a (~sym f) "'(" (v~ u) ")")]
      [(list 'diff u x)
       #:when (and (symbol? u) (member x (output-differentiation-mark))) (~a (v~ u #t) "' ")]
      [(list 'diff u x)
       #:when (member x (output-differentiation-mark)) (~a "(" (v~ u #t) ")' ")]
      [(list 'diff u  x)                      (~a "\\dv{" (~var x) "}(" (v~ u #t) ") ")]
      
      [(Equal u v) (~a (v~ u #t) (~sym '=) (v~ v #t))]
      [(Log u)     ((output-format-log) u)]
      [(Log u v)   ((output-format-log) u v)]
      [(Up u v)    ((output-format-up)  u v)]
      [(Piecewise us vs)    (case (length us)
                              [(1) (let ([u (first us)] [v (first vs)])
                                     (~a (v~ u) " , " (v~ v)))]
                              [else
                               (string-append*
                                (append (list "\\begin{cases}\n")
                                        (for/list ([u us] [v vs])
                                          (~a (v~ u) " & " (v~ v) "\\\\\n"))
                                        (list "\\end{cases}")))])]
      [(list 'sqrt u)   ((output-format-sqrt) u)]   ; unnormalized sqrt
      [(list 'root u v) ((output-format-root) u v)] ; unnormalized root
      [(list 'percent u) (~a (v~ u) (~sym '|%|))]

      [(list 'abs u)      ((output-format-abs) u)] 
      [(list 'vec u)      (~a "\\overrightarrow{" (v~ u) "}")] ; TODO: only for TeX 
      [(list 'vecfun u v) (~a "\\overrightarrow{" (v~ u) "}" "(" (v~ v) ")" )]
      [(list 'deg u)      (~a (v~ u) "° ")]                    ; TODO: only for TeX 
      [(list 'hat u)      (~a "\\hat{" (v~ u) "}")]            ; TODO: only for TeX
      [(list 'bar u)      (~a "\\bar{" (v~ u) "}")]            ; TODO: only for TeX
      [(list 'where u v)  (~a (v~ u) " | " (v~ v))]        ; TODO: only for TeX

      [(list 'int u v)   (~a "\\int " (v~ u) "\\ \\textrm{d}" (v~ v))] ; TODO: only for TeX
      
      [(list* 'braces  us) (apply ~a (append (list "\\{") (add-between (map v~ us) ",") (list "\\}")))] ; TODO: only for TeX 
      [(list* 'bracket us) (apply ~a (append (list   "[") (add-between (map v~ us) ",") (list "]")))] ; TODO: only for TeX 

      [(list (or 'ccinterval 'ocinterval 'cointerval 'oointerval ) v1 v2)
             ((output-interval) u)]

      [(app: f us) #:when (memq f '(< > ≤ ≥ <= >= Less LessEqual Greater GreaterEqual))
                   (match us [(list u v) (~a (v~ u) (~relop f) (v~ v))])]
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
  (check-equal? (~ '(* -1 4)) "$-4$")
  (check-equal? (~ (normalize '(/ x (- 1 (expt y 2))))) "$\\frac{x}{1-y^{2}}$")
  (check-equal? (~ '(* -8 x )) "$-8x$")
  (check-equal? (~ '(- 1 (+ 2 3))) "$1-(2+3)$")
  (check-equal? (~ '(* -1 (expt (- x 1) 2))) "$-(x-1)^{2}$")
  (check-equal? (~ '(* 4 (+ -7 (* -1 a)))) "$4(-7-a)$")
  (check-equal? (~ '(* 3 6)) "$3\\cdot 6$")
  (check-equal? (~ '(sqrt d)) "$\\sqrt{d}$")
  (check-equal? (~ '(* (sqrt d) a)) "$\\sqrt{d}\\cdot a$")
  (check-equal? (~ '(* -4 (expt -1 3))) "$-4\\cdot {(-1)}^{3}$")
  (check-equal? (~ '(* -9 (expt x -10))) "$\\frac{-9}{x^{10}}$")
  (check-equal? (~ '(- (* 2 3) (* -1  4))) "$2\\cdot 3-(-4)$")
  (check-equal? (~ '(- (* 2 3) (* -1 -4))) "$2\\cdot 3-(-(-4))$")
  (check-equal? (~ '(* -1 (* (- x 1) (- x 2)))) "$-(x-1)\\cdot (x-2)$")
  (check-equal? (~ '(paren -3)) "${\\left(-3\\right)}$")
  (check-equal? (~ '(red  (paren -3))) "${\\color{red}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(blue (paren -3))) "${\\color{blue}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(green  (paren -3))) "${\\color{green}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(purple (paren -3))) "${\\color{purple}{\\left(-3\\right)}\\color{black}}$")
  (check-equal? (~ '(paren x_1 y_1))   "${\\left(x_1,y_1\\right)}$")
  (check-equal? (~ '(~ X (bi n p)))    "$X \\approx  \\text{bi}(n,p)$")
  (check-equal? (~ '(* 1/2 1/3))               "$\\frac{1}{2}\\cdot \\frac{1}{3}$")
  (check-equal? (~ '(sqrt (* 1/2 1/3))) "$\\sqrt{\\frac{1}{2}\\cdot \\frac{1}{3}}$")
  (check-equal? (~ '(sqrt (* 12 1/12 11/12))) "$\\sqrt{12\\cdot \\frac{1}{12}\\cdot \\frac{11}{12}}$")
  (parameterize ([output-root? #t]) (check-equal? (~ '(expt 2 1/3)) "$\\sqrt[3]{2}$"))
  (check-equal? (tex '(- (sqr c) (sqr a))) "$c^{2}-a^{2}$")
  (check-equal? (tex '(Less         x 1)) "$x< 1$")
  (check-equal? (tex '(LessEqual    x 1)) "$x≤ 1$")
  (check-equal? (tex '(Greater      x 1)) "$x> 1$")
  (check-equal? (tex '(GreaterEqual x 1)) "$x≥ 1$")
  (check-equal? (tex '(bar x))            "$\\bar{x}$")
  (check-equal? (tex '(braces 1 2 3))     "$\\{1,2,3\\}$")
  (check-equal? (tex '(bracket 1 2 3))    "$[1,2,3]$")
  ;; Names
  (check-equal? (tex 'a)                     "$a$")
  (check-equal? (tex 'ab)                    "$\\mathrm{ab}$")
  (check-equal? (tex 'a_1)                   "$a_1$")
  (check-equal? (tex 'ab_1)                  "$\\mathrm{ab}_1$")
  (check-equal? (tex 'h_a)                   "$h_a$")
  (check-equal? (tex 'mellemliggende-vinkel) "$\\mathrm{mellemliggende\\;vinkel}$")
  (check-equal? (tex '(= T (* 1/2 a b (sin C))))  "$T = \\frac{1}{2}ab\\cdot \\sin(C)$")
  (check-equal? (tex '(* 1/2 a b c))              "$\\frac{1}{2}abc$")
  (check-equal? (parameterize ([output-implicit-product? #t]) (tex '(* 5 (sqrt 5))))
                "$5\\sqrt{5}$")  
  (check-equal? (let ()
                  (use-tex-output-style)
                  (parameterize ([output-implicit-product? #f]) (~ '(* 5 (sqrt 5)))))
                "$5\\cdot \\sqrt{5}$")  
  (check-equal? (tex '(= (sin A) (/ (* 5 (sqrt 5)) 2)))
                "$\\sin(A) = \\frac{5\\sqrt{5}}{2}$")
  (check-equal? (parameterize ([output-format-negative-exponent #t]) (tex `(expt 2 -1)))
                "${2}^{-1}$") ; a^-1 is a special case
  (check-equal? (parameterize ([output-format-negative-exponent #t]) (tex `(expt 2 -3)))
                "${2}^{-3}$") ; a^p, p negative
  (check-equal? (parameterize ([output-format-negative-exponent #t]) (tex `(expt 2 -1)))
                "${2}^{-1}$")
  (check-equal? (parameterize ([output-format-negative-exponent #t]) (tex `(expt 2 -2)))
                "${2}^{-2}$")
  (check-equal? (parameterize ([output-format-negative-exponent #t] [output-use-quotients? #f]) 
                  (tex '(expt y -4)))
                "${y}^{-4}$")

  #;(check-equal? (tex '(expt (expt a 2) 3))    ; note: a^2^3 is a "double superscript error"
                "${a^{2}}^3$")
  (check-equal? (parameterize ([output-format-negative-exponent #t] [output-use-quotients? #f]) 
                  (tex '(expt (expt a 2) -3)))    ; note: a^2^3 is a "double superscript error"
                "${a^{2}}^{-3}$")
  #;(check-equal? (parameterize ([output-format-negative-exponent #t] [output-use-quotients? #f]) 
                  (tex '(expt (expt a -2) -3)))    ; note: a^2^3 is a "double superscript error"
                "${a^{-2}}^{-3}$")
  #;(check-equal? (parameterize ([output-format-negative-exponent #t] [output-use-quotients? #f]) 
                  (tex '(expt (expt a -2) 3)))    ; note: a^2^3 is a "double superscript error"
                  "${a^{-2}}^3$")
  (check-equal? (tex '(expt (/ a b) 5))
                "${(\\frac{a}{b})}^{5}$")
  (check-equal? (tex '(expt 2 1))
                "$2^{1}$")
  

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
  (check-equal? (parameterize ([output-format-negative-exponent #t] [output-use-quotients? #f]) 
                  (~ '(expt (/ a b) -2))) "(a/b)^(-2)")
  (check-equal? (~ '(expt (* (expt a 2) (expt b 3)) 4))
                "(a^2*b^3)^4")
  (check-equal? (~ '(expt 1/2 2)) "(1/2)^2")
  (check-equal? (~ '(* 3 (expt 1/2 2))) "3*(1/2)^2")
  ; implict multiplaction between numbers and vectors
  (check-equal? (tex '(* 2 (up 3 4))) "$2\\begin{pmatrix} 3\\\\4\\end{pmatrix}$")
  (check-equal? (tex '(+ (* 2 (up 3 4)) (vec b))) "$2\\begin{pmatrix} 3\\\\4\\end{pmatrix}+\\overrightarrow{b}$")
  )
