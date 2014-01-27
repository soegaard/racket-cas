#lang at-exp racket/base

(require scribble/eval
         scribble/manual
         (for-syntax racket/base))

(provide author-jens-axel
         make-plain-cas-eval
         make-cas-eval)

(define (author-jens-axel)
  @author{@(author+email "Jens Axel Søgaard" "jensaxel@soegaard.net")})

(define (make-plain-cas-eval)
  (define eval (make-base-eval))
  (eval '(require racket))
  (eval '(require racket-cas))
  eval)

(define (make-cas-eval)
  (define eval (make-plain-cas-eval))
  (eval '(require math/scribblings/rename-defines))
  (λ (v)
    (cond [(syntax? v)  (eval #`(rename-defines #,v))]
          [(list? v)    (eval `(rename-defines ,v))]
          [else         (eval v)])))

(define-syntax (rename-defines stx)
  (syntax-case stx ()
    [(_ e)
     (let ([expanded  (local-expand #'e (syntax-local-context) #f)])
       (syntax-case expanded (define-values)
         [(define-values (x ...) expr)
          (with-syntax ([(y ...)  (generate-temporaries #'(x ...))])
            (syntax/loc stx
              (begin
                (define-syntax x (make-rename-transformer #'y)) ...
                (define-values (y ...) expr))))]
         [_  #'e]))]))