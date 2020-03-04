#lang racket/base

(provide current-simplify)

(define current-simplify  (make-parameter (λ (u) u))) ; set to simplify  in "simplify-expand.rkt"
