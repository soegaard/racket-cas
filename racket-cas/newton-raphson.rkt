#lang racket/base
(provide newton-raphson
         bf-newton-raphson)

;;;
;;; Newton-Raphson
;;;

; Newton-Raphson is an algorithm for finding roots
; Given a funktion f(x) the algorithm attempts to find a solution to:
;     f(x)=0
; The search starts at u0.

; URL https://en.wikipedia.org/wiki/Newton%27s_method


(require math/bigfloat
         "core.rkt" "runtime-paths.rkt"
         "diff.rkt"
         "simplify-expand.rkt") ; for subst
(define normalize (dynamic-require normalize.rkt      'normalize))
(define N         (dynamic-require numerical-evaluation.rkt 'N))
(define bf-N      (dynamic-require numerical-evaluation.rkt 'bf-N))

(define (newton-raphson f x u0 [n 10] #:trace? [trace? #f])
  ; Use Newton-Raphson's metod to solve the equation f(x)=0.
  ; The starting point is u0. The number of iterations is n.
  ; The expressions f and u0 must be normalized.
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

(module+ test
  (require rackunit)
  ; Let's compute sqrt(2) using standard floating points.
  (check-= (newton-raphson (normalize '(- (sqr x) 2.)) 'x 1.0 #:trace? #f)
           (sqrt 2)
           1e-14)

  ; Let's try again, but this time use bigfloats.
  ; Remember: the precision 200 is in bits... not number of decimal digits.
  ; > (bf-precision 200) (bfsqrt (bf 2))
  ; (bf #e1.4142135623730950488016887242096980785696718753769480731766796)
  (check-equal? (bf-newton-raphson (normalize '(- (sqr x) 2.)) 'x 2. #:precision 200 #:trace? #f)
                (let ([old (bf-precision)])
                  (bf-precision 200)
                  (begin0 (bfsqrt (bf 2)) (bf-precision old))))
  )
