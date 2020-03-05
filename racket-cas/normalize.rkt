#lang racket/base
(provide normalize)
;;;
;;; Normalization
;;;


(require racket/match math/bigfloat
         (except-in "bfracket.rkt" denominator numerator)
         "core.rkt" "math-match.rkt" "parameters.rkt" "compose-app.rkt"
         "logical-operators.rkt")

(module+ test
  (require rackunit math/bigfloat "parameters.rkt")
  (define x 'x) (define y 'y) (define z 'z))


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
    [(Atan u)           (Atan (n u))] 
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
