#lang racket/base
(provide Equal Less LessEqual Greater GreaterEqual)

;;;
;;; Relational Operators
;;; 

(require racket/list racket/match 
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require "normalize.rkt" 'normalize))
  (define x 'x) (define y 'y) (define z 'z))


;;;
;;; Relational Operators
;;;

(define-match-expander Equal
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Equal: u v)] [_ (identifier? stx) #'Equal:])))

(define-match-expander Less
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '< u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Less: u v)] [_ (identifier? stx) #'Less:])))

(define-match-expander LessEqual
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '<= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(LessEqual: u v)] [_ (identifier? stx) #'LessEqual:])))

(define-match-expander Greater
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '> u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Greater: u v)] [_ (identifier? stx) #'Greater:])))

(define-match-expander GreaterEqual
  (λ (stx) (syntax-parse stx [(_ u v) #'(list '>= u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(GreaterEqual: u v)] [_ (identifier? stx) #'GreaterEqual:])))


(define (Equal:        u v) (math-match* (u v) [(r s) (=  r s)] [(_ __) `(=  ,u ,v)]))
(define (Less:         u v) (math-match* (u v) [(r s) (<  r s)] [(_ __) `(<  ,u ,v)]))
(define (LessEqual:    u v) (math-match* (u v) [(r s) (<= r s)] [(_ __) `(<= ,u ,v)]))
(define (Greater:      u v) (math-match* (u v) [(r s) (>  r s)] [(_ __) `(>  ,u ,v)]))
(define (GreaterEqual: u v) (math-match* (u v) [(r s) (>= r s)] [(_ __) `(>= ,u ,v)]))
