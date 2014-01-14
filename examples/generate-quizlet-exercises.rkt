#lang racket
;;;
;;; This example generates exercises of the form:
;;;    (ax+b)^2 = a^x^2 +2abx +b^2
;;; The output format is ready for import at quizlet.com.
;;;
;;; See:    http://quizlet.com/33695503/scatter
;;;

(require "../racket-cas.rkt")

(define (poly->string p x [var "x"])
  (define (sign r) 
    (match r
      [r #:when (number? r) (if (>= r 0) "+" "-" )]
      [s #:when (symbol? s) "+"]
      [(list '* n s)        (sign n)]
      [(list '* n a s) #:when (symbol? a) (sign n)]
      [(list 'expt s n)     "+"]
      [else (error 'sign (~a "got: " r))]))
  (define (Abs r) 
    (match r
      [r #:when (number? r) (abs r)]
      [s #:when (symbol? s) s]
      [(list '* n s)        (list '* (abs n) s)]
      [(list '* n a s)      (list '* (abs n) a s)]
      [(list 'expt s n)     (list 'expt s n)]
      [else (error 'abs (~a "got: " r))]))

  (define (exponent->string var n)
    (cond [(= n 0) ""]
          [(= n 1) var]
          [(= n 2) (~a var "²")]
          [else    (~a var "^" n)]))
  (define (doit terms)
    (let* ([sign-coef-exps
            (for/list ([term (in-list (reverse terms))])
              (match-define (list i ci) term)
              (let ([es   (exponent->string var i)]
                    [signs (sign ci)]
                    [cis   (if (number? ci)
                               (~a (abs ci))
                               (match (Abs ci)
                                 [(list 'expt var 2) (~a var "²")]
                                 [(list '* n var)    (~a n var)]
                                 [(list '* n var var2)  (~a n var var2)]
                                 [_                  (~a ci)]))])
                (cond
                  [(= i 0)                      (list signs cis "")]
                  [(and (number? ci) (= ci  1)) (list "+" "" es)]
                  [(and (number? ci) (= ci -1)) (list "-" "" es)]
                  [else                         (list signs cis es)])))])
      (define (space x)
        (if (equal? x "") "" (~a " " x)))
      (match sign-coef-exps
        [(list) "0"]
        [(list (list sign coef exps) more ...)
         (string-append 
          ; first term
          (if (equal? sign "+") "" sign) 
          (if (equal? sign "+") coef (space coef))
          exps
          ; remaining terms
          (apply string-append
                 (map (match-lambda
                        [(list sign coef exps)
                         (~a (space sign) (space coef) exps)])
                      more)))])))
  ; convert to (i ci) form
  (doit (for/list ([c (coefficient-list p x)]
                   [n (in-naturals)]
                   #:unless (equal? x 0))
          (list n c))))

(define (random-first-order-polynomial max-coef #:allow-variables [allow-variables #f])
  (local-require math/base)
  (define (X)   (random-integer (- max-coef) (+ max-coef 1)))
  (define (X≠0) (match (X) [x #:when (zero? x) (Y)] [x x]))
  (define (V)   (define vars '(a b)) (list-ref vars (random (length vars))))
  (define (Y) (if (and allow-variables (zero? (random 2))) (V) (X≠0)))
  (define a (Y))
  (define b (if (equal? a 1) (Y) (X≠0)))
  (normalize `(+ (* ,a x) ,b)))

(define (generate-question1)
  ; (4x - 1)² ; 16x² - 8x + 1
  (define ax+b (random-first-order-polynomial 5))
  (~a "(" (poly->string ax+b x) ")² ; " 
      (poly->string (expand (normalize `(sqr ,ax+b))) x)))

(define (generate-question2)
  ; (ax - 4)² ; a²x² - 8ax + 16
  (define ax+b (random-first-order-polynomial 5 #:allow-variables #t))
  (~a "(" (poly->string ax+b x) ")² ; " 
      (poly->string (expand (normalize `(sqr ,ax+b))) x)))

(define (questions generate-question n)
  (define (loop qs)
    (cond [(= (set-count qs) n) qs]
          [else (loop (set-add qs (generate-question)))]))
  (for ([q (loop (set))]) (displayln q)))

(questions generate-question2 100)
