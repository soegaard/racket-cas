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
  (define (sign r) (if (>= r 0) "+" "-"))
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
                    [cis   (~a (abs ci))])
                (cond
                  [(= i 0)   (list signs cis "")]
                  [(= ci  1) (list "+" "" es)]
                  [(= ci -1) (list "-" "" es)]
                  [else      (list signs cis es)])))])
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
                   #:unless (zero? c))
          (list n c))))

(define (random-first-order-polynomial max-coef)
  (local-require math/base)
  (define (X) (random-integer (- max-coef) (+ max-coef 1)))
  (define (Y) (match (X) [x #:when (zero? x) (Y)] [x x]))
  (define a (Y))
  (define b (if (= a 1) (Y) (X)))
  (normalize `(+ (* ,a x) ,b)))

(define (question)
  (define ax+b (random-first-order-polynomial 5))
  (~a "(" (poly->string ax+b x) ")² ; " 
      (poly->string (expand (normalize `(sqr ,ax+b))) x)))

(define (questions n)
  (define (loop qs)
    (cond [(= (set-count qs) n) qs]
          [else (loop (set-add qs (question)))]))
  (for ([q (loop (set))]) (displayln q)))

(questions 100)