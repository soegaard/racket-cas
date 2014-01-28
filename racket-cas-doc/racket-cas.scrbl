#lang scribble/manual
@(require scribble/eval "doc-utils.rkt")
@(define cas-eval (make-cas-eval))

@title[#:tag "top"]{Racket CAS}

@defmodule[racket-cas]

@(author-jens-axel)

CAVEAT: This documentation is under creation and is far from complete.
See the file @racket[racket-cas.rkt] for a complete list of available
functions.

The @racketmodname[racket-cas] library provides functions for 
working with symbolic expressions.

@section[#:tag "racket-cas:ref"]{Function Reference}

@defproc[(distribute [u symbolic-expression]) symbolic-expression]{
Apply the distribute law to the symbolic expression @racket[u].
Distribute applies the law to all sub expressions.
}
@interaction[#:eval cas-eval
  (distribute '(+  (* 2 (+ a b))  (* (+ a b) 3)  (sin (* 4 (+ a b)))))]

@defproc[(normalize [u symbolic-expression]) ase]{
Returns a normalized version of the symbolic expression @racket[u].
In other words @racket[normalize] runs the automatic simplifier on
the expression @racket[u] and returns an expression in ASE form.
}
@interaction[#:eval cas-eval
                    (normalize '(+ 1 x 2 y x 3))]

@defproc[(polynomial [u symbolic-expression] [x symbolic-expression]) boolean]{
Returns @racket[#t] if @racket[u] is a polynomial in @racket[x].
Note that @racket[x] need not be a variable, it can be an arbitrary expression.
}
@interaction[#:eval cas-eval
                    (polynomial? (normalize '(+ (* 3 x x) (* 7 x) -2)) x)
                    (polynomial? (normalize '(/ x a)) x)
                    (polynomial? (normalize '(/ x a)) 'a)
                    (polynomial? (normalize '(+ (sin x) (expt (sin x) 3))) x)
                    (polynomial? (normalize '(+ (sin x) (expt (sin x) 3))) '(sin x))]
                    
                    
                    
                    
                    