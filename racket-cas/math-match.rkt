#lang racket
(provide math-match* math-match :pat)
(require (for-syntax racket/string racket/match racket/syntax)         
         rackunit)

(module+ test (require rackunit))

(module predicates racket 
  (provide exact-natural? @e? @pi?  @i? inexact-number? exact-number? bigfloat-number? positive-number? negative-number?
           inexact-number-or-bigloat?)
  (require math/bigfloat)
  (define (exact-number? x)   (and (number? x) (exact? x)))
  (define (exact-natural? x)  (and (exact-number? x) (integer? x) (>= x 0)))
  (define (inexact-number? x) (and (number? x) (inexact? x)))
  (define (inexact-number-or-bigloat? x) (or (and (number? x) (inexact? x)) (bigfloat? x)))
  (define (bigfloat-number? x) (bigfloat? x))
  (define (positive-number? x) (and (real? x) (positive? x)))
  (define (negative-number? x) (and (real? x) (negative? x)))
  (define (@e?  u) (eq? u '@e))  ; Euler's constant
  (define (@pi? u) (eq? u '@pi)) ; pi
  (define (@i?  u) (eq? u '@i))) ; i

(module conventions racket
  (provide find-convention-type conventions  (struct-out convention))
  (require racket/stxparam (for-template racket (submod ".." predicates)))
  ; A CONVENTION consists of a predicate 
  ;   pred? : string -> boolean
  ; and a syntax object representing an identifier
  ; bound to a predicate e.g #'number?
  (struct convention (pred? type))
  
  (define (make-begins-with-pred s)
    (λ (t) (regexp-match (~a "^" s) t)))
  
  (define (make-ends-with-pred s)
    (λ (t) (regexp-match (~a s "$") t)))
  
  (define (make-ends-with-not-equal-pred s)
    (λ (t) (and (not (equal? t s)) (regexp-match (~a (regexp-quote s) "$") t))))
  
  (define (ends-with-dot? t)
    (and (regexp-match "\\.$" t) (not (equal? t "..."))))
  
  (define (make-is-pred s)
    (λ (t) (equal? s t)))
  
  (define conventions
    (list (convention ends-with-dot?                      #'inexact-number-or-bigloat?)
          (convention (make-ends-with-pred ".0")          #'inexact-number?)
          (convention (make-ends-with-pred ".bf")         #'bigfloat-number?)
          (convention (make-ends-with-not-equal-pred "+") #'positive-number?)
          (convention (make-ends-with-not-equal-pred "-") #'negative-number?)
          (convention (make-begins-with-pred "x")         #'symbol?)
          (convention (make-begins-with-pred "y")         #'symbol?)
          (convention (make-begins-with-pred "z")         #'symbol?)
          (convention (make-begins-with-pred "r")         #'number?)
          (convention (make-begins-with-pred "s")         #'number?)
          (convention (make-begins-with-pred "m")         #'exact-natural?)
          (convention (make-begins-with-pred "n")         #'exact-natural?)
          (convention (make-begins-with-pred "p")         #'integer?)
          (convention (make-begins-with-pred "q")         #'integer?)
          (convention (make-begins-with-pred "α")         #'exact-number?)
          (convention (make-begins-with-pred "β")         #'exact-number?)
          ; note: a and b are used to match general expressions,
          ;       so we need to pick something else to match booleans
          (convention (make-begins-with-pred "bool") #'boolean?)
          (convention (make-is-pred "@e")  #'@e?)
          (convention (make-is-pred "@pi") #'@pi?)
          (convention (make-is-pred "@i")  #'@i?)))
  
  (define (find-convention-type-list s)
    (for/list ([c (in-list conventions)]
               #:when ((convention-pred? c) s))
      (convention-type c)))

  (define (find-convention-type s)
    (define type-lst (find-convention-type-list s))
    (if (empty? type-lst)
        #f
        (with-syntax ([(a ...) type-lst])
          (syntax (conjoin a ...)))
        )))
  
(module+ test (require (submod ".." conventions))
  (check-equal? (syntax->datum (find-convention-type "r")) '(conjoin number?))
  (check-equal? (syntax->datum (find-convention-type "p+")) '(conjoin positive-number? integer?))
  (check-equal? (syntax->datum (find-convention-type "x")) '(conjoin symbol?))
  (check-equal? (find-convention-type "foo") #f)
  (check-equal? (syntax->datum (find-convention-type "x.bf")) '(conjoin bigfloat-number? symbol?))
  (check-equal? (syntax->datum (find-convention-type "n.0")) '(conjoin inexact-number? exact-natural?)))

(module math-match racket
  (provide math-match math-match* :pat)
  (require racket/match racket/match/stxtime
           (for-syntax racket/match racket/match/stxtime (submod ".." conventions))
           (for-syntax racket/syntax))
  
  (define-match-expander :pat
    (λ (stx)
      (define (rewrite-id pat)
        (let* ([pat-sym (syntax->datum pat)]
               [pat-str (symbol->string pat-sym)])
          (define pred (find-convention-type pat-str))
          (cond [pred
                 (with-syntax ([pred pred]
                               [name (datum->syntax pat pat-sym)])
                   #'(? pred name))]
                [else pat])))
      (define (rewrite pat0)
        (syntax-case pat0 ()
          [pat (identifier? #'pat) (rewrite-id #'pat)]
          [pat #'pat]))
      (syntax-case stx (? app)
        [(_ pat) (and (identifier? #'pat) (match-expander? (syntax-local-value #'pat (λ()#f))))
                 #'pat]
        [(_ pat) (identifier? #'pat) (rewrite-id #'pat)]
        [(_ #(pat ...))           (syntax/loc stx (vector (:pat pat) ...))]
        [(_ (? pred pat))         (with-syntax ([p (rewrite #'pat)])
                                    (syntax/loc stx (? pred p)))]
        [(_ (== pat))             (with-syntax ([p #'pat])
                                    (syntax/loc stx (== p)))]; pat can be outer variable, so don't rewrite it
        [(_ (app expr pats ...))  (with-syntax ([(p ...) (map rewrite (syntax->list #'(pats ...)))])
                                    (syntax/loc stx (app expr pats ...)))]
        [(_ (pat0 pat ...))       (and (identifier? #'pat0) 
                                       (match-expander? (syntax-local-value #'pat0 (λ()#f))))
                                  (syntax/loc stx (pat0 (:pat pat) ...))]
        [(_ (pat0 pat ...))    (with-syntax ([(p ...) (map rewrite (syntax->list #'(pat0 pat ...)))])
                                 (syntax/loc stx (p ...)))]
        [(_ pat)                #'pat])))
  
  (define-syntax (math-match stx)
    (syntax-case stx ()
      [(_ val-expr [pat . more] ...)
       (with-syntax ([so #'stx]
                     [(new-pat ...) 
                      (for/list ([pat-stx (in-list (syntax->list #'(pat ...)))])
                        (datum->syntax pat-stx `(:pat ,(syntax->datum pat-stx))))])
         (syntax/loc stx (match/derived val-expr stx [new-pat . more] ...)))]))
  
  (define-syntax (math-match* stx)
    (syntax-case stx ()
      [(_ (val-expr ...) [pats . more] ...)
       (with-syntax ([so #'stx]
                     [((new-pat ...) ...) 
                      (for/list ([ps (in-list (syntax->list #'(pats ...)))])
                        (for/list ([pat (in-list (syntax->list ps))])
                          (datum->syntax ps `(:pat ,(syntax->datum pat)))))])
         (syntax/loc stx (match*/derived (val-expr ...) stx [(new-pat ...) . more] ...)))])))

(module+ test (require (submod ".." math-match) math/bigfloat)
  (check-equal? (math-match (list 1 1.2 'x) [(list n r x) (list n r x)]) (list 1 1.2 'x))
  (check-equal? (math-match 1.2 [n 1] [r 2]) 2)
  (check-equal? (math-match 'x [n 1] [r 2] [x 3]) 3)
  (check-equal? (math-match 7 [x 3] [n 1] [r 2]) 1)
  (check-equal? (math-match 7.4  [x 3] [n 1] [r 2]) 2)
  (check-equal? (math-match '(1 a) [(list r x) (list r x)]) '(1 a))
  (check-equal? (math-match '(1 2) [(list r s) (list r s)]) '(1 2))
  (check-equal? (math-match 1   [@e 2] [_ 3]) 3)
  (check-equal? (math-match '@e [@e 2] [_ 3]) 2)
  (check-equal? (math-match 2 [n.0 3] [_ 4]) 4)
  (check-equal? (math-match 2.0 [n.0 3] [_ 4]) 4) ; '(conjoin inexact-number? exact-natural?)
  (check-equal? (math-match (bf 2.0) [x.bf 3] [_ 4]) 4) ; '(conjoin bigfloat-number? symbol?)
  (check-equal? (let ((x 'x)) (math-match 'x [(== x) #t] [_ #f])) #t)
  (check-equal? (math-match -42   [p+ #f] [p- #t] [_ #f]) #t)
  (check-equal? (math-match -42.5 [p+ #f] [p- #t] [_ #f]) #f)  ; p- only negative integers
  (check-equal? (math-match -42.5 [r+ #f] [r- #t] [_ #f]) #t)) 

(require (submod "." math-match))
(require (for-syntax syntax/parse))

