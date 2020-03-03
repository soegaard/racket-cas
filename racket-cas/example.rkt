#lang racket/base

(require racket/format
         "racket-cas.rkt")

;;;
;;; Examples
;;;

(define x 'x) (define y 'y) (define z 'z) (define h 'h)

(define (examples)
  (let ()
    (displayln "Is tan'(x) = 1 +tan(x)^2 ?")
    (equal? (diff (Tan x) x) (expand (⊕ 1 (Sqr (Tan x))))))
  (let ()
    (displayln "Proof of (x^2)' = 2x.")
    (define (f x) (⊗ x x))
    (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
    (define Δy/h (expand (⊘ Δy h)))
    (displayln (limit Δy/h h 0))) ; evaluates to (* 2 x)  
  (let ()
    (displayln "Proof of (x^3)' = 3x^2")
    (define (f x) (⊗ x x x))
    (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
    (define Δy/h (expand (⊘ Δy h)))
    (displayln (limit Δy/h h 0))) ; evaluates to (* 3 (expt x 2))  
  (let () 
    (displayln "Symmetric polynomials in 4 variables")
    (map displayln 
         (map expand 
              (coefficient-list (for/⊗ ([xi '(x1 x2 x3 x4)]) 
                                       (⊕ 1 (⊗ xi x))) x))))
  #;'(1
      (+ x1 x2 x3 x4)
      (+ (* x1 x2) (* x1 x3) (* x1 x4) (* x2 x3) (* x2 x4) (* x3 x4))
      (+ (* x1 x2 x3) (* x1 x2 x4) (* x1 x3 x4) (* x2 x3 x4))
      (* x1 x2 x3 x4))  
  (let () ; Pascal's triangle
    (displayln "Pascal's triangle")
    (for/list ([n 10]) 
      (displayln (coefficient-list (normalize `(expt (+ x 1) ,n)) x)))
    (void))
  (let ()
    (let ([u (expand '(* (- x 1) (expt (- x 2) 2) (- x 4)))])
      (define eqn (Equal u 0))
      (displayln (~a "Solving: " eqn))
      (displayln (solve eqn x)))
    ; Solving: (= (+ 16 (* -36 x) (* 28 (expt x 2)) (* -9 (expt x 3)) (expt x 4)) 0)
    ; '(or (= x 2) (= x 2) (= x 4) (= x 1))
    ))


;(require latex-pict pict)
;(define (render u)
;  (define (strip$ x) (substring x 1 (- (string-length x) 1)))
;  (pict->bitmap (scale (tex-math (strip$ (tex u))) 2)))


;;; Example from the REPL.

; Require start makes ' automatically normalize all expressions.

; (displayln "Enter the following in the REPL to redefine ' to do automatic simplification.")
; (write '(require (submod "." start))) (newline)
;> (require (submod "." start))
;> '(+ x 1)
;'(+ 1 x)
;> '(+ x 1 y)
;'(+ 1 x y)
;> (limit '(sin x) x 0)
;0
;> (limit '(cos x) x 0)
;1
;> '(expt (+ x y) 3)
;'(expt (+ x y) 3)
;> (expand '(expt (+ x y) 2))
;'(+ (expt x 2) (expt y 2) (* 2 x y))
;> (render '(+ x 1))
; ...

  

;; ;;;
;; ;;; Examples
;; ;;;

;; (define x 'x) (define y 'y) (define z 'z) (define h 'h)

;; (define (examples)
;;   (let ()
;;     (displayln "Is tan'(x) = 1 +tan(x)^2 ?")
;;     (equal? (diff (Tan x) x) (expand (⊕ 1 (Sqr (Tan x))))))
;;   (let ()
;;     (displayln "Proof of (x^2)' = 2x.")
;;     (define (f x) (⊗ x x))
;;     (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
;;     (define Δy/h (expand (⊘ Δy h)))
;;     (displayln (limit Δy/h h 0))) ; evaluates to (* 2 x)  
;;   (let ()
;;     (displayln "Proof of (x^3)' = 3x^2")
;;     (define (f x) (⊗ x x x))
;;     (define Δy   (expand (⊖ (f (⊕ x h)) (f x))))
;;     (define Δy/h (expand (⊘ Δy h)))
;;     (displayln (limit Δy/h h 0))) ; evaluates to (* 3 (expt x 2))  
;;   (let () 
;;     (displayln "Symmetric polynomials in 4 variables")
;;     (map displayln 
;;          (map expand 
;;               (coefficient-list (for/⊗ ([xi '(x1 x2 x3 x4)]) 
;;                                        (⊕ 1 (⊗ xi x))) x))))
;;   #;'(1
;;       (+ x1 x2 x3 x4)
;;       (+ (* x1 x2) (* x1 x3) (* x1 x4) (* x2 x3) (* x2 x4) (* x3 x4))
;;       (+ (* x1 x2 x3) (* x1 x2 x4) (* x1 x3 x4) (* x2 x3 x4))
;;       (* x1 x2 x3 x4))  
;;   (let () ; Pascal's triangle
;;     (displayln "Pascal's triangle")
;;     (for/list ([n 10]) 
;;       (displayln (coefficient-list (normalize `(expt (+ x 1) ,n)) x)))
;;     (void))
;;   (let ()
;;     (let ([u (expand '(* (- x 1) (expt (- x 2) 2) (- x 4)))])
;;       (define eqn (Equal u 0))
;;       (displayln (~a "Solving: " eqn))
;;       (displayln (solve eqn x)))
;;     ; Solving: (= (+ 16 (* -36 x) (* 28 (expt x 2)) (* -9 (expt x 3)) (expt x 4)) 0)
;;     ; '(or (= x 2) (= x 2) (= x 4) (= x 1))
;;     ))

;; (module+ start
;;   (provide quote quasiquote)
;;   (require (submod ".."))
;;   (require (prefix-in old: (only-in racket/base quote quasiquote)))
;;   ; In the REPL it can be convenient to change the meaning of ' 
;;   ; to automatic normalization:
;;   (define-syntax (quote stx) 
;;     (syntax-case stx () [(_ . datum) #'(normalize (old:quote . datum))]))
;;   (define-syntax (quasiquote stx) 
;;     (syntax-case stx () [(_ . datum) #'(normalize (old:quasiquote . datum))])))

;; ; (let () (define f '(* x x)) `(* x ,f))  

;; ; This macro doesn't work as expected ... why?
;; (define-syntax (repl stx) 
;;   (syntax-case stx () 
;;     [_ (with-syntax ([req (datum->syntax stx 'require)])
;;          (syntax/loc stx (req (submod "." start))))]))

;; ;(require latex-pict pict)
;; ;(define (render u)
;; ;  (define (strip$ x) (substring x 1 (- (string-length x) 1)))
;; ;  (pict->bitmap (scale (tex-math (strip$ (tex u))) 2)))


;; ;;; Example from the REPL.

;; ; Require start makes ' automatically normalize all expressions.

;; ; (displayln "Enter the following in the REPL to redefine ' to do automatic simplification.")
;; ; (write '(require (submod "." start))) (newline)
;; ;> (require (submod "." start))
;; ;> '(+ x 1)
;; ;'(+ 1 x)
;; ;> '(+ x 1 y)
;; ;'(+ 1 x y)
;; ;> (limit '(sin x) x 0)
;; ;0
;; ;> (limit '(cos x) x 0)
;; ;1
;; ;> '(expt (+ x y) 3)
;; ;'(expt (+ x y) 3)
;; ;> (expand '(expt (+ x y) 2))
;; ;'(+ (expt x 2) (expt y 2) (* 2 x y))
;; ;> (render '(+ x 1))
;; ; ...
