#lang racket/base

(provide current-simplify default-output-implicit-product?)

(define current-simplify  (make-parameter (λ (u) u))) ; set to simplify  in "simplify-expand.rkt"

(define default-output-implicit-product? (make-parameter #t))
