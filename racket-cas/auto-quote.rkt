#lang racket/base
(require (for-syntax racket/base syntax/parse racket/syntax))

(define-syntax (auto-top stx)
  (syntax-parse stx
    [(top . top-id)
     (syntax/loc stx
       'top-id)]))

(provide (rename-out [auto-top #%top]))
