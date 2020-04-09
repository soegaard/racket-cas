#lang racket/base
(provide diff  ; (diff u x)  differentiate the expression u with respect to the variable x
         Diff) 

;;;
;;; Differentiation
;;;

(require racket/format racket/match 
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "relational-operators.rkt" "trig.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))

(define (1/sqrt:1-u^2 u)
  (⊘ 1 (Sqrt (⊖ 1 (Sqr u)))))

(define (diff u x)
  (define (d u) (diff u x))
  (define (products us)
    ; example: (products '(a b c)) = '((* a b c) (* b c) c)
    (match us
      ['()          '()]
      [(list u)     (list u)] 
      [(cons u us)  (define ps (products us))
                    (cons (⊗ u (car ps)) ps)]))
  
  (math-match u
    [r 0]
    [y #:when (eq? x y) 1]
    [y 0]
    [(⊕ v w)     (⊕ (d v) (d w))]
    [(⊗ v w)     (match u
                   [(list '* v w) (⊕ (⊗ (d v) w) (⊗ v (d w)))]
                   [(list '* vs ...)
                    (let loop ([sum     0]
                               [us    '()]
                               [us⊗     1]
                               [ws    vs]
                               [ws⊗s  (products vs)])
                      ; invariant: (append us ws)       = vs
                      ; invariant: (⊗ us⊗ (first ws⊗s)) = u
                      (match ws
                        ['()                                                sum]
                        [(list w)          (⊕ (⊗ (d w)    us⊗)              sum)]
                        [(cons w ws) (loop (⊕ (⊗ (d w) (⊗ us⊗ (cadr ws⊗s))) sum)
                                           (cons u w) (⊗ us⊗ w) ws (cdr ws⊗s))]))])]
    [(Expt u r)  (⊗ r (Expt u (- r 1)) (d u))]
    [(Expt @e u) (⊗ (Exp u) (d u))]
    [(Expt r y)  #:when (and (positive? r) (equal? y x))  (⊗ (Expt r x) (Ln r))]
    [(Expt u v)  (diff (Exp (⊗ v (Ln u))) x)] ; assumes u positive    
    ; [(Exp u)   (⊗ (Exp u) (d u))]
    [(Ln u)    (⊗ (⊘ 1 u) (d u))]
    [(Cos u)   (⊗ (⊖ 0 (Sin u)) (d u))]
    [(Sin u)   (⊗ (Cos u) (d u))]
    [(Asin u)     (1/sqrt:1-u^2 u)]
    [(Acos u)  (⊖ (1/sqrt:1-u^2 u))]
    [(Atan u)  (⊘ 1 (⊕ (Sqr x) 1))]
    [(Si x)    (Sinc x)]
    [(Ci x)    (⊘ (Cos x) x)]
    [(app: f us)  #:when (symbol? f)
                  (match us
                    [(list u) (cond [(eq? u x)  (Diff `(,f ,x) x)]
                                    [else       (⊗ `(app (deriviative ,f ,x) ,u) (d u))])] ; xxx
                    [_ `(diff (,f ,@us) ,x)])]           ; xxx
    [_ (error 'diff (~a "got: " u " wrt " x))]))

(define (Diff: u [x 'x])
  (define D Diff:)
  (math-match u
    [(Equal u1 u2) (Equal (D u1 x) (D u2 x))]
    [_             (list 'diff u x)]))

(define-match-expander Diff
  (λ (stx) (syntax-parse stx [(_ u x) #'(list 'diff u x)]))
  (λ (stx) (syntax-parse stx [(_ u x) #'(Diff: u)] [_ (identifier? stx) #'Diff:])))



(module+ test
  (displayln "TEST - diff")
  (check-equal? (diff 1 x) 0)
  (check-equal? (diff x x) 1)
  (check-equal? (diff y x) 0)
  (check-equal? (diff (⊗ x x) x) '(* 2 x))
  (check-equal? (diff (⊗ x x x) x) '(* 3 (expt x 2)))
  (check-equal? (diff (⊗ x x x x) x) '(* 4 (expt x 3)))
  (check-equal? (diff (⊕ (⊗ 5 x) (⊗ x x)) x) '(+ 5 (* 2 x)))
  (check-equal? (diff (Exp x) x) (Exp x))
  (check-equal? (diff (Exp (⊗ x x)) x) (⊗ 2 x (Exp (⊗ x x))))
  (check-equal? (diff (Expt x 1) x) 1)
  (check-equal? (diff (Expt x 2) x) (⊗ 2 x))
  (check-equal? (diff (Expt x 3) x) (⊗ 3 (Expt x 2)))
  (check-equal? (diff (Ln x) x) (⊘ 1 x))
  (check-equal? (diff (Ln (⊗ x x)) x) (⊘ (⊗ 2 x) (⊗ x x)))
  (check-equal? (diff (Cos x) x) (⊖ (Sin x)))
  (check-equal? (diff (Cos (⊗ x x)) x) (⊗ (⊖ (Sin (⊗ x x))) 2 x))
  (check-equal? (diff (Sin x) x) (Cos x))
  (check-equal? (diff (Sin (⊗ x x)) x) (⊗ 2 (Cos (Expt x 2)) x))
  ; TODO: ASE should rewrite the result to (* '(expt x x) (+ 1 (ln x)))
  (check-equal? (diff (Expt x x) x) '(* (expt @e (* x (ln x))) (+ 1 (ln x))))
  (check-equal? (diff (Si x) x) (Sinc x))
  (check-equal? (diff (Ci x) x) (⊘ (Cos x) x))
  )
