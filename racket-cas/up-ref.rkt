#lang racket/base
(provide Up Ref)

;;;
;;; Tuples (aka column vectors)
;;;

(require racket/match racket/math
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "normalize.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define x 'x) (define y 'y) (define z 'z))



; Tuples (aka column vectors)
(define-match-expander Up
  (λ (stx) (syntax-parse stx [(_ u ...) #'(list 'up u ...)]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(Up:      u ...)] [_ (identifier? stx) #'Up:])))

(define (Up: . us)  
  `(up ,@us))

(module+ test
  (check-equal? (Up 2 3) '(up 2 3)))


(define-match-expander Ref
  (λ (stx) (syntax-parse stx [(_ u i) #'(list 'ref u i)]))
  (λ (stx) (syntax-parse stx [(_ u i) #'(Ref:      u i)] [_ (identifier? stx) #'Ref:])))

(define (Ref: u i)
  (cond
    [(natural? i) (match u
                    [(Up us ...) (if (< i (length us)) (list-ref us i) `(ref ,u ,i))])]
    [else `(ref ,u ,i)]))


(module+ test
  ; Tuple indices are zero based
  (check-equal? (Ref (Up 2 3) 0) 2)
  (check-equal? (Ref (Up 2 3) 1) 3))

