#lang racket
(require math/bigfloat math/flonum (prefix-in % racket) (prefix-in % math/base))

(define-syntax (define-fun stx)
  (syntax-case stx ()
    [(_ name %name bfname)
     (syntax/loc stx 
       (begin
         (provide name)
         (define (name x)
           (cond  
             [(number? x)   (%name x)]
             [(bigfloat? x) (bfname x)]
             [else          `(name ,x)]))))]))

(define-fun sin %sin bfsin)
(define-fun cos %cos bfcos)
(define-fun tan %tan bftan)

(define-fun asin %asin bfasin)
(define-fun acos %acos bfacos)
(define-fun atan %atan bfatan)

(define-fun sinh %sinh bfsinh)
(define-fun cosh %cosh bfcosh)
(define-fun tanh %tanh bftanh)

(define-fun asinh %asinh bfasinh)
(define-fun acosh %acosh bfacosh)
(define-fun atanh %atanh bfatanh)

(define-fun exp %exp bfexp)
(define-fun ln  %log bflog)

(define-fun sqr  %sqr  bfsqr)
(define-fun abs  %abs  bfabs)
(define-fun sgn  %sgn  bfsgn)
(define-fun sqrt %sqrt bfsqrt)

(define-fun zero? %zero? bfzero?)
(define-fun positive? %positive? bfpositive?)
(define-fun negative? %negative? bfnegative?)
(define-fun integer?  %integer?  bfinteger?)
(define-fun even?     %even?     bfeven?)
(define-fun odd?      %odd?      bfodd?)
(define-fun rational? %rational? bfrational?)
(define-fun infinite? %infinite? bfinfinite?)
(define-fun nan?      %nan?      bfnan?)

(define-fun truncate  %truncate  bftruncate)
(define-fun floor     %floor     bffloor)
(define-fun ceiling   %ceiling   bfceiling)
(define-fun round     %round     bfround)

; bffrac
; bfrint

(define-syntax (define-fun2 stx)
  (syntax-case stx ()
    [(_ name %name bfname)
     (syntax/loc stx 
       (begin
         (provide name)
         (define (name x y)
           (cond  
             [(and (number? x)   (number?   y)) (%name  x y)]
             [(and (bigfloat? x) (bigfloat? y)) (bfname x y)]
             [(and (number? x)   (bigfloat? y)) (name x (bigfloat->flonum y))]
             [(and (bigfloat? x) (number?   y)) (name (bigfloat->flonum x) y)]
             [else `(name ,x ,y)]))))]))

(define-fun2 = %= bf=)
(define-fun2 > %> bf>)
(define-fun2 < %< bf<)
(define-fun2 >= %>= bf>=)
(define-fun2 <= %<= bf<=)

(define-fun2 expt %expt bfexpt)

(provide log)
(define (log b [x #f])
  (let ([b (if x b 10)]
        [x (if x x b)])
    (cond
      [(and (number? b) (number? x))
       (cond [(= b 10) (/ (%log x) (%log 10))]
             [(= b  2) (/ (%log x) (%log  2))]
             [else     (/ (%log x) (%log  b))])]
      [(and (bigfloat? b) (bigfloat? x))
       (cond [(bf= b 10.bf) (bflog10 x)]
             [(bf= b  2.bf) (bflog2 x)]
             [else          (bf/ (bflog x) (bflog b))])]
      [(and (number? b) (bigfloat? x))
       (log b (bigfloat->flonum x))]
      [(and (bigfloat? b) (number? x))
       (log (bigfloat->flonum b) x)]
      [else `(log ,b ,x)])))

(provide max)
(define (max . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap real? xs)     (apply %max xs)]
    [(andmap bigfloat? xs) (apply bfmax xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(real? x)     (%max m x)]
         [(bigfloat? x) (%max m (bigfloat->flonum x))]
         [else (error 'max (~a "number or bigfloat expected, got: " x))]))]))

(provide min)
(define (min . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap real? xs)     (apply %min xs)]
    [(andmap bigfloat? xs) (apply bfmin xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(real? x)     (%min m x)]
         [(bigfloat? x) (%min m (bigfloat->flonum x))]
         [else (error 'min (~a "number or bigfloat expected, got: " x))]))]))

(provide +)
(define (+ . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap real? xs)     (%sum xs)]
    [(andmap bigfloat? xs) (apply bf+ xs)]
    [else
     (for/fold ([m 0.0]) ([x (in-list xs)])
       (cond
         [(real? x)     (%+ m x)]
         [(bigfloat? x) (%+ m (bigfloat->flonum x))]
         [else (error '+ (~a "number or bigfloat expected, got: " x))]))]))

(provide *)
(define (* . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap real? xs)     (apply %* xs)]
    [(andmap bigfloat? xs) (apply bf* xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(real? x)     (%* m x)]
         [(bigfloat? x) (%* m (bigfloat->flonum x))]
         [else (error '* (~a "number or bigfloat expected, got: " x))]))]))

(provide -)
(define (- . xs)
  (define (->flonum x) (if (bigfloat? x) (bigfloat->flonum x) x))
  (cond 
    [(andmap real? xs)     (apply %- xs)]
    [(andmap bigfloat? xs) (apply bf- xs)]
    [else
     (for/fold ([m (->flonum (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(real? x)     (%- m x)]
         [(bigfloat? x) (%- m (bigfloat->flonum x))]
         [else (error '- (~a "number or bigfloat expected, got: " x))]))]))

(provide /)
(define (/ . xs)
  (define (->real x) (if (bigfloat? x) (bigfloat->real x) x))
  (cond 
    [(andmap real? xs)     (apply %/ xs)]
    [(andmap bigfloat? xs) (apply bf/ xs)]
    [else
     (for/fold ([m (->real (first xs))]) ([x (in-list (rest xs))])
       (cond
         [(real? x)     (%/ m x)]
         [(bigfloat? x) (%/ m (bigfloat->real x))]
         [else (error '/ (~a "number or bigfloat expected, got: " x))]))]))

(provide numerator)
(define (numerator x) ; this follows Maxima and MMA 
  (if (or (number? x) (bigfloat? x))
      (if (or (bigfloat? x) (inexact? x))
          x
          (%numerator x))
      (error 'numerator (~a "number or bigfloat expected, got: " x))))

(provide denominator)
(define (denominator x) ; this follows Maxima and MMA
  (if (or (number? x) (bigfloat? x))
      (if (or (bigfloat? x) (inexact? x))
          1
          (%denominator x))
      (error 'denominator (~a "number or bigfloat expected, got: " x))))



