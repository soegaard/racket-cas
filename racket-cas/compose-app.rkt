#lang racket/base
(provide Compose     ; function composition
         App         ; function application
         Piecewise   ; piecewise function   
         Piecewise:) 

;;;
;;; Functions
;;;


(require racket/list racket/match
         (for-syntax racket/base racket/syntax syntax/parse)
         "core.rkt" "math-match.rkt" "parameters.rkt" "runtime-paths.rkt")

(define normalize (dynamic-require normalize.rkt       'normalize))

(module+ test
  (require rackunit math/bigfloat )
  (define subst     (dynamic-require simplify-expand.rkt 'subst))
  
  (define x 'x) (define y 'y) (define z 'z))


(define-match-expander Compose
  (λ (stx) (syntax-parse stx [(_ u v) #'(list 'compose u v)]))
  (λ (stx) (syntax-parse stx [(_ u v) #'(Compose:      u v)] [_ (identifier? stx) #'Compose:])))

(define (Compose: u v)
  `(compose ,u ,v))

(module+ test
  (displayln "TEST - Compose")
  (check-equal? (Compose 'f 'g) '(compose f g)))


; Application
(define-match-expander App
  (λ (stx) (syntax-parse stx [(_ u ...) #'(list 'app u ...)]))
  (λ (stx) (syntax-parse stx [(_ u ...) #'(App:      u ...)] [_ (identifier? stx) #'App:])))

(define (App: u . us)
  ; (displayln (list 'u u 'us us))
  (match u
    [(list 'up coords ...) `(up ,@(for/list ([coord coords]) (apply App: coord us)))]
    [(list 'compose u v)   (match us
                             [(list w) (App u (App v w))]
                             [_        `(app ,u ,@us)])]
    ; [(list* u vs)          (normalize (list* u vs))]
    [_                     `(app ,u ,@us)]))



;;; Piecewise 

;;; The pattern (Piecewise us vs) matches a piecewise expression of
;;; the form (piecewise [u v] ...) 
;;; and binds us to (list u ...) 
;;; and binds vs to (list v ...) 
(define-match-expander Piecewise
  (λ (stx)
    (syntax-case stx ()
      [(_ u c)
       #'(list 'piecewise (list u c) (... ...))]))
  (λ (stx)
    (syntax-case stx ()
      [(_ (u v) ...) #'(list 'piecewise (list u v) ...)]
      [_ (identifier? stx) #'piecewise])))

(define-syntax (piecewise stx)
  (syntax-parse stx
    [(_ [u:expr v:expr] ...)
     (syntax/loc stx (cond [v u] ...))]))

(define (Piecewise: us vs) ; assume us and vs are canonical
  (define simplify (current-simplify))
  (define clauses
    ; simplify and remove clauses where the conditional is false
    (for/list ([u us] [v (map simplify vs)] #:when v)
      (list u v)))
  ; if one of the conditional expressions v is true,
  ; then the result is the corresponding u.
  (define first-true    
    ; wrapped in list to disguish non-true and first true v has false u
    (let loop ([uvs clauses])      
      (match uvs
        ['()                     #f]
        [(list* (list u #t) uvs) (list u)]
        [_                       (loop (rest uvs))])))
  (match first-true
    [(list u) u]
    [_        (cons 'piecewise clauses)]))



(module+ test
  (displayln "TEST - piecewise")
  (define u (normalize '(piecewise [(- x 1) (<= x 0)] [(sqr x) (> x 0)])))
  (check-equal? u '(piecewise ((+ -1 x) (<= x 0)) ((expt x 2) (> x 0))))
  (check-equal? (subst u 'x  3)  9)
  (check-equal? (subst u 'x -2) -3)
  (check-equal? (subst u 'x  0) -1))




