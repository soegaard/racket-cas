#lang racket/base
(provide Or  And
         Or: And:)

;;;
;;; Logical Operators
;;; 

(require racket/list racket/match 
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt")

(module+ test
  (require rackunit math/bigfloat)
  (define normalize (dynamic-require "normalize.rkt" 'normalize))
  (define x 'x) (define y 'y) (define z 'z))

;; And

(define-match-expander Or
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'or u v) (list-rest 'or u (app (λ(ys) (cons 'or ys)) v)))]
      [(_ u)       #'(list 'or u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(Or: u ...)] [_ (identifier? stx) #'Or:])))


(define (Or: . us)
  (match us
    ['() #f]
    [_  (let/ec return
          (define (flatten us)
            (reverse 
             (for/fold ([vs '()])
                       ([u (in-list us)])
               (match u
                 [#t             (return #t)]
                 [#f             vs]
                 [(list* 'or ws) (append vs (map flatten ws))]
                 [_              (cons u vs)]))))
          (match (remove-duplicates (flatten us))
            ['()        #f]
            [(list v)   v]
            [vs         `(or ,@(sort vs <<))]))]))
      

(module+ test 
  (check-equal? (normalize '(or (= x 3) (or (= x 2) (= x 1)))) '(or (= x 1) (= x 2) (= x 3)))
  (check-equal? (normalize '(or (= x 1) (= x 2) (= x 1))) '(or (= x 1) (= x 2))))


;; And

(define-match-expander And
  (λ (stx)
    (syntax-parse stx
      [(_ u v) #'(or (list 'and u v) (list-rest 'and u (app (λ(ys) (cons 'and ys)) v)))]
      [(_ u)       #'(list 'and u)]))
  (λ(stx) (syntax-parse stx [(_ u ...) #'(And: u ...)] [_ (identifier? stx) #'And:])))

(define (And: . us)
  (match us
    ['() #t]
    [_  (let/ec return
          (define (flatten us)
            (reverse 
             (for/fold ([vs '()]) ([u (in-list us)])
               (match u
                 [#t              vs]
                 [#f              (return #f)]
                 [(list* 'and ws) (append vs (map flatten ws))]
                 [_               (cons u vs)]))))
          (match (remove-duplicates (flatten us))
            ['()        #t]
            [(list v)   v]
            [vs         `(and ,@(sort vs <<))]))]))

(module+ test 
  (check-equal? (normalize '(and (= x 3) (and (= x 2) (= x 1)))) '(and (= x 1) (= x 2) (= x 3)))
  (check-equal? (normalize '(and (= x 1) (= x 2) (= x 1)))       '(and (= x 1) (= x 2))))
