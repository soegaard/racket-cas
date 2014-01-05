#lang racket
(provide math-match* math-match :pat)
(require (for-syntax racket/string racket/match racket/syntax)         
         rackunit)

(module+ test (require rackunit))

(module predicates racket (provide natural? @e? @pi?)
  (define (natural? x) (and (integer? x) (>= x 0)))
  (define (@e? u)  (eq? u '@e))   ; Euler's constant
  (define (@pi? u) (eq? u '@pi))) ; pi

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
  
  (define (make-is-pred s)
    (λ (t) (equal? s t)))
  
  (define conventions
    (list (convention (make-begins-with-pred "x") #'symbol?)
          (convention (make-begins-with-pred "y") #'symbol?)
          (convention (make-begins-with-pred "z") #'symbol?)
          (convention (make-begins-with-pred "r") #'number?)
          (convention (make-begins-with-pred "s") #'number?)
          (convention (make-begins-with-pred "m") #'natural?)
          (convention (make-begins-with-pred "n") #'natural?)
          (convention (make-is-pred "@e")  #'@e?)
          (convention (make-is-pred "@pi") #'@pi?)))
  
  (define (find-convention-type s)
    (for/or ([c (in-list conventions)])
      (and ((convention-pred? c) s)
           (convention-type c)))))

(module+ test (require (submod ".." conventions))
  (check-equal? (syntax->datum (find-convention-type "r")) 'number?)
  (check-equal? (syntax->datum (find-convention-type "x")) 'symbol?)
  (check-equal? (find-convention-type "foo") #f))

(module math-match racket
  (provide math-match math-match* :pat)
  (require (for-syntax racket/match racket/match/stxtime (submod ".." conventions))
           (for-syntax racket/syntax))
  (define-match-expander :pat
    (λ (stx)
      (define (rewrite-id pat)
        (let* ([pat-sym (syntax->datum pat)]
               [pat-str (symbol->string pat-sym)])
          (define pred (find-convention-type pat-str))
          (cond [pred (with-syntax ([pred pred]
                                    [name (datum->syntax stx pat-sym)])
                        #'(? pred name))]
                [else pat])))
      (define (rewrite pat0)
        (syntax-case pat0 ()
          [pat (identifier? #'pat) (rewrite-id #'pat)]
          [pat #'pat]))
      (syntax-case stx ()
        [(_ pat) (and (identifier? #'pat) (match-expander? #'pat)) #'pat]
        [(_ pat) (identifier? #'pat) (rewrite-id #'pat)]
        [(_ #(pat ...))      (syntax/loc stx (vector (:pat pat) ...))]
        [(_ (pat0 pat ...))  (with-syntax ([(p ...) (map rewrite (syntax->list #'(pat0 pat ...)))])
                               (syntax/loc stx (p ...)))]
        [(_ pat)             #'pat])))
  
  (define-syntax (math-match stx)
    (syntax-case stx ()
      [(_ val-expr [pat . more] ...)
       (with-syntax ([(new-pat ...) 
                      (for/list ([pat-stx (in-list (syntax->list #'(pat ...)))])
                        (datum->syntax pat-stx `(:pat ,(syntax->datum pat-stx))))])
         (syntax/loc stx (match/derived val-expr stx [new-pat . more] ...)))]))
  
  (define-syntax (math-match* stx)
    (syntax-case stx ()
      [(_ (val-expr ...) [pats . more] ...)       
       (with-syntax ([((new-pat ...) ...) 
                      (for/list ([ps (in-list (syntax->list #'(pats ...)))])
                        (for/list ([pat (in-list (syntax->list ps))])
                          (datum->syntax pat `(:pat ,(syntax->datum pat)))))])
         (syntax/loc stx (match*/derived (val-expr ...) stx [(new-pat ...) . more] ...)))])))

(module+ test (require (submod ".." math-match))
  (check-equal? (math-match (list 1 1.2 'x) [(list n r x) (list n r x)]) (list 1 1.2 'x))
  (check-equal? (math-match 1.2 [n 1] [r 2]) 2)
  (check-equal? (math-match 'x [n 1] [r 2] [x 3]) 3)
  (check-equal? (math-match 7 [x 3] [n 1] [r 2]) 1)
  (check-equal? (math-match 7.4  [x 3] [n 1] [r 2]) 2)
  (check-equal? (math-match '(1 a) [(list r x) (list r x)]) '(1 a))
  (check-equal? (math-match '(1 2) [(list r s) (list r s)]) '(1 2))
  (check-equal? (math-match 1   [@e 2] [_ 3]) 3)
  (check-equal? (math-match '@e [@e 2] [_ 3]) 2))

(require (submod "." math-match))
