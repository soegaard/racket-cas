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

@section[#:tag "racket-cas:installation"]{Installation}

Clone the racket-cas repository from Github:

@tt{git clone https://github.com/soegaard/racket-cas.git}

Open DrRacket and paste the path to racket-cas into the
"Source Path" text field - then click the "Install" button.

@section[#:tag "racket-cas:introduction"]{Introduction}
RacketCAS is a computer algebra system written in Racket.
The system allows you to manipulate and compute with symbolic expressions.
The representation of symbolic expressions were chosen to be very simple:

@verbatim|{
A SYMBOLIC EXPRESSION is :
   <sym> ::= <num> | <var> | (<var> <sym> ...)
where
   <num> is a Racket number
   <var> is a Racket symbol

Expressions of the form (<var> <sym> ...) will be called applications.

The following symbols have special meanings:

    @e   Euler's constant
    @pi  pi
    @n   stands for an arbitrary natural number
    @p   stands for an arbitrary integer

The symbols @e and @pi are recognized in input.
The symbols @n and @p can occur in output.
  }|

The representation was chosen to make it easy to use RacketCAS as a library.

A few examples:

@verbatim|{
  RacketCAS                              Mathematics
      1                                       1
      x                                       x
   (+ x y 1)                                x+y+1
   (sqrt (+ (expt a 2) (expt b 2)))      sqrt(a^2 + b^2)
   }|

If you prefer to use standard infix notation to input symbolic
expressions, you can combine RacketCAS with a parser like
@tt{https://github.com/soegaard/infix}.

Each mathematical expression can be represented by many symbolic expressions.
As a simple example consider the mathematical expression @tt{y-x}.
Some of the possibilities: @racket[(- y x)], @racket[(+ y (* -1 x))], and, @racket[(+ (* -1 x) y)].

In a CAS it is important to have an unique way of representing an expression.
For one comparing two symbolic expressions for equality is greatly simplified
when an unique representation is used.

The canonical representation of an expression is called a @emph{normal form}.
The process of rewriting an expression into its normal form is called @emph{normalization}.
Internally most operations of a CAS work on normal forms. Use the function @racket[normalize]
to rewrite a an expression into its normal form.

Example: The expressions @tt{y-x}, @tt{y+(-1)x}, and @tt{(-1)x+y} have the same
normal form. The expressions are therefore equal.
@interaction[#:eval cas-eval
  (normalize '(- y x))
  (normalize '(+ y (* -1 x)))
  (normalize '(+ (* -1 x) y))]

If you are using RacketCAS interactively, it is convenient to change the meaning
of quote such that it calls normalize automatically. Simply require the start
module:
@interaction[#:eval cas-eval                    
  '(- y x)
  (require (submod racket-cas/racket-cas start))
  '(- y x)]





@section[#:tag "racket-cas:ref"]{Function Reference}

@defproc[(distribute [u symbolic-expression]) symbolic-expression]{
Apply the distributive law to the symbolic expression @racket[u].
Distribute applies the law to all sub expressions.
}
@interaction[#:eval cas-eval
  (distribute '(+  (* 2 (+ a b))  (* (+ a b) 3)  (sin (* 4 (+ a b)))))]

@defproc[(ln [u symbolic-expression]) symbolic-expression]{
Return the natural logarithm of the expression @racket[u].
The natural logarithm uses Euler's number @emph{e} as the base.
                                                           
@interaction[#:eval cas-eval
             (normalize '(ln \@e))
             (normalize '(ln (expt \@e 2)))
             (normalize '(ln (* x (expt \@e 2))))]
 }

@defproc*[ ([(log                         [u symbolic-expression]) symbolic-expression]
           [(log [v symbolic-expression] [u symbolic-expression]) symbolic-expression])]{
The logarithm of the expression @racket[u]. The expression @racket[v] if present is used
as the base. If the optional base is omitted, base 10 is assumed.

@interaction[#:eval cas-eval
             (normalize '(log 100))
             (normalize '(log (expt 10 x)))
             (normalize '(expt 10 (log x)))
             (normalize '(log 2 8))
             (normalize '(log (* (expt 10 3) z)))]
 }

           

@defproc[(N [u symbolic-expression]) symbolic-expression]{
Evaluate the expression @racket[u] numerically. Use standard Racket reals
(i.e. double precision IEEE floating point numbers) to compute the value of the expression.
@interaction[#:eval cas-eval
             (N '(/ 2 3))
             (N '\@pi)
             (N (subst '(expt (+ x 1) 5) x \@pi))]
}

@defproc[(bf-N [u symbolic-expression] [prec #f]) symbolic-expression]{
Like @racket[N] but use Racket big floats. If the optional argument @racket[prec]
is present, the computation will be done with bigfloat precision @racket[prec].
If omitted the precision will use the value of @racket[bf-precision] as the precision.
Note: The bigfloat precision is (roughly) the number of bits used in the bigfloat representation.

@interaction[#:eval cas-eval
             (bf-N '\@pi 5)
             (bf-N '\@pi 100)]             
}


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

@interaction[#:eval cas-eval
                    (polynomial? (normalize '(+ (* 3 x x) (* 7 x) -2)) x)
                    (polynomial? (normalize '(/ x a)) x)
                    (polynomial? (normalize '(/ x a)) 'a)
                    (polynomial? (normalize '(+ (sin x) (expt (sin x) 3))) x)
                    (polynomial? (normalize '(+ (sin x) (expt (sin x) 3))) '(sin x))]
}

@defproc[(sqr [u symbolic-expression]) symbolic-expression]{
Compute the square of the expression @racket[u].
@interaction[#:eval cas-eval
             (normalize '(sqr 3))
             (normalize '(sqr (+ x 1)))]
 }

@defproc[(taylor [u symbolic-expression] [x symbol] [a number] [n natural]) symbolic-expression]{
Compute the @racket[n]'th degree Taylor polynomial of the expression @racket[u] with respect
to the variable @racket[x] around @tt{x=a}.
@interaction[#:eval cas-eval
             (taylor (normalize '(expt \@e x)) 'x 0 3)
             (taylor (normalize '(/ (expt t 2) (+ t 1))) 't 0 5)]
}

