#lang racket/base
(provide Magnitude
         Angle
         ExpI
         ; ---
         ComplexRealExpt     ; used by Expt
         ComplexComplexExpt  ; used by Expt
         RealComplexExpt)    ; used by Expt

;;;
;;; Complex Expressions
;;;

(require racket/list racket/match racket/math
         (prefix-in % "bfracket.rkt")
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "trig.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require "normalize.rkt"            'normalize))
  (define N         (dynamic-require "numerical-evaluation.rkt" 'N))
  (define x 'x) (define y 'y) (define z 'z))


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

(define (ComplexRealExpt Expt a b c) ; d=0
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

(define (RealComplexExpt Expt r a b)
  (when debugging? (displayln (list 'RealComplexExpt r a b)))
  ; r^z = e^ln(r)^z = e^(z ln(r)) = e^((a+ib) ln(r)) 
  ;                               = e^(a ln(r)) * e^(i b ln(r))) = r^a * e^(i b ln(r)))
  (⊗ (Expt r a) (Exp (⊗ b @i (Ln r)))))

(define (ComplexComplexExpt Expt a b c d)
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
