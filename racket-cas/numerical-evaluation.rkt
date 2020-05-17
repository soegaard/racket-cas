#lang racket/base
(provide N bf-N)

;;;
;;; Numeric evalution
;;;

(require racket/list racket/match
         (only-in racket/math pi)
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "runtime-paths.rkt"
         "logical-operators.rkt" "relational-operators.rkt" "trig.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require normalize.rkt 'normalize))
  (define x 'x) (define y 'y) (define z 'z))


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
    [(Deg u)     (M deg Deg u)]
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
  (real-mode)
  (check-equal?   (normalize '(expt -8 1/3))  -2)
  
  (complex-mode)
  (check-equal?   (normalize '(expt -8 1/3))        '(* 2 (+ (* @i 1/2 (expt 3 1/2)) 1/2)))
  (check-=     (N (normalize '(expt -8      1/3)))  1+1.732i 0.0001) ; principal value 1+sqrt(3)i instead of 2i
  (check-=     (N (normalize '(expt -8+i -173/3))) (expt  -8+i -173/3) 0.0001)
  ; turn the default back on
  (real-mode))

  
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
