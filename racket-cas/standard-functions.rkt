#lang racket/base
; (provide)   define-function automatically exports the function name
;;;
;;; Functions
;;;

(require racket/match math/bigfloat
         math/number-theory
         math/special-functions ; gamma
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt"
         (except-in "bfracket.rkt" denominator numerator)
         "math-match.rkt")
; (define normalize (dynamic-require "normalize.rkt"      'normalize))

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))

;;;
;;; Functions
;;;

(define-syntax (define-function stx)
  (syntax-parse stx
    [(_ Name Name: sym-name expr)
     (syntax/loc stx
       (begin
         (provide Name)
         (define-match-expander Name
           (λ (stx) (syntax-parse stx [(_ u) #'(list 'sym-name u)]))
           (λ (stx) (syntax-parse stx [(_ u) #'(Name: u)] [_ (identifier? stx) #'Name:])))
         (define Name: expr)))]))


(define-function Gamma Gamma: gamma
  (λ (u)
    (math-match u
      [n    (gamma n)]
      [p    'undefined]
      [r    (gamma r)]
      [r.bf (bfgamma r.bf)]
      [_    `(gamma ,u)])))


;;;
;;; Integer Functions
;;;

(define-syntax (define-integer-function stx)
  (syntax-parse stx
    [(_ Name Name: name)
     (syntax/loc stx
       (define-function Name Name: name
         (λ (u)
           (math-match u
             [n (name n)]
             [_ `(name ,u)]))))]))

(define-integer-function Factorial Factorial: factorial)
(define-integer-function Prime? Prime?: prime?)
(define-integer-function Odd-prime? Odd-prime?: odd-prime?)
(define-integer-function Nth-prime Nth-prime: nth-prime)
(define-integer-function Random-prime Random-prime: random-prime)
(define-integer-function Next-prime Next-prime: next-prime)
(define-integer-function Prev-prime Prev-prime: prev-prime)
(define-integer-function Divisors divisors: divisors)
