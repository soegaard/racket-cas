#lang racket
;;;
;;; Racket CAS
;;;

; The file "racket-cas.rkt" got too large, so this is branch ("refactor")
; is an attempt to split racket-cas up in smaller pieces.

; The plan of attack.

; 1. Rename "racket-cas.rkt" to "core.rkt"
; 2. Let "racket-cas.rkt" require and provide everything from "racket-cas.rkt".
; 3. Slowly move pieces from "racket-cas.rkt" to other files.


; Module dependencies:

; repl -> racket-cas -> core

(require               "core.rkt" "diff.rkt" "format.rkt" "limit.rkt" "newton-raphson.rkt" "polynomial.rkt" "solve.rkt" "taylor.rkt")
(provide (all-from-out "core.rkt" "diff.rkt" "format.rkt" "limit.rkt" "newton-raphson.rkt" "polynomial.rkt" "solve.rkt" "taylor.rkt"))

(require               "up-ref.rkt" "compose-app.rkt" "normalize.rkt" "simplify-expand.rkt")
(provide (all-from-out "up-ref.rkt" "compose-app.rkt" "normalize.rkt" "simplify-expand.rkt"))


(module+ start
  (provide quote quasiquote)
  (require (submod ".."))
  (require (prefix-in old: (only-in racket/base quote quasiquote)))
  ; In the REPL it can be convenient to change the meaning of ' 
  ; to automatic normalization:
  (define-syntax (quote stx) 
    (syntax-case stx () [(_ . datum) #'(normalize (old:quote . datum))]))
  (define-syntax (quasiquote stx) 
    (syntax-case stx () [(_ . datum) #'(normalize (old:quasiquote . datum))])))

; (let () (define f '(* x x)) `(* x ,f))  

; This macro doesn't work as expected ... why?
(define-syntax (repl stx) 
  (syntax-case stx () 
    [_ (with-syntax ([req (datum->syntax stx 'require)])
         (syntax/loc stx (req (submod "." start))))]))


