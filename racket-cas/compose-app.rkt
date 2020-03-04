#lang racket/base
(provide Compose ; function composition
         App)    ; function application

;;;
;;; Functions
;;;


(require racket/match
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))


(define-match-expander Compose
  (λ (stx) (syntax-parse stx [(_ u v) #'(list 'compose u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Compose:      u v)] [_ (identifier? stx) #'Compose:])))

(define (Compose: u v)
  `(compose ,u ,v))

(module+ test
  (displayln "TEST - Compose")
  (check-equal? (Compose 'f 'g) '(compose f g)))


; Application
(define-match-expander App
  (λ (stx) (syntax-parse stx [(_ u ...) #'(list 'app u ...)]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(App:      u ...)] [_ (identifier? stx) #'App:])))

(define (App: u . us)
  (match u
    [(list 'up coords ...) `(up ,@(for/list ([coord coords]) (apply App: coord us)))]
    [(list 'compose u v)   (match us
                             [(list w) (App u (App v w))]
                             [_        `(app ,u ,@us)])]                              
    [_                     `(app ,u ,@us)]))
