racket-cas
==========

A Simple Computer Algebra System (CAS) for Racket
-------------------------------------------------

Here is a short example. Open racket-cas.rkt in DrRacket and run it.

To begin write:
    > (require racket-cas/repl)
note: if that fails use
    > (require (submod "." start))
    
This changes the meaning of quote such that automatic simplifier
will simplify all quoted and quasi-quoted expressions.
    > '(+ x 2 a 3 (* 4 x))
    '(+ 5 a (* 5 x))

The Taylor series of sin(x) around x=2 of degree 3:
    > (taylor '(sin x) x 2 3)
    '(+ (* -1/2 (expt (+ -2 x) 2) (sin 2)) (* -1/6 (expt (+ -2 x) 3)
(cos 2)) (* (+ -2 x) (cos 2)) (sin 2))

Since (sin 2) can not be represented exactly it is not evaluated
numerically. Use N (for numeric) to force numeric evaluation:
    > (N (expand (taylor '(sin x) x 2 3)))
    '(+  -0.6318662024609201
       (* 2.2347416901985055         x)
      (* -0.8707955499599832 (expt x 2))
      (* 0.0693578060911904  (expt x 3)))

An alternative is to use 2.0 instead of 2.
   > (expand (taylor '(sin x) x 2.0 3))
   <same result>
This works since 2.0 is an inexact number, and inexactness is contagious.

We expect the Taylor series around 2.0 approximates sin(x) for x near 2.0.
Let's compare the Taylor series in 2.1 with sin(2.1).

First we substitute the x in the Taylor series with 2.1.
    > (subst (expand (N (taylor '(sin x) x 2 3))) x 2.1)
    0.8632056138429305
The we calculate sin(2.1) for comparision:
    > (sin 2.1)
    0.8632093666488738

To show that Racket CAS also supports bigfloats (floating point 
numbers with an arbitrary number of decimals), let's see what
the result is with a precision of 100 binary decimals:
    > (bf-N (taylor '(sin x) x 2 3) 100 x (bf 2.1))
    (bf #e0.86320561384293019376447471077597)

We can use standard plot library to draw a few graphs of the Taylor polynomials.
The plot library expects standard Racket functions from number to number.
The function  compile  will turn a symbolic expression into a normal Racket function.
    > (require plot)
    > (plot (list (function (compile (taylor '(sin x) x 0 5)) #:color "green")
                  (function sin #:color "red" -3.14 3.14)))
    <nice graphs appear in DrRacket>

Let's compare Taylor polynomials of various orders.
    > (plot (append (for/list ([n 6]) (function (compile (taylor '(cos x) x pi n)) #:color (+ n 1)))
                    (list (function cos #:color "red")))
            #:x-min (- pi) #:x-max (* 3 pi) #:y-min -2 #:y-max 2)
     <graphs appear>

Racket CAS can compute limits for x->a where a is a real number.
The  limit  function will apply l'Hospital's rule if neccessary (upto 10 times).
Standard high school limits therefore work:
    > (limit '(/ (sin x) x) x 0)
   1

For anyone interested in contributing to the code, the main file is racket-cas/racket-cas.rkt.
In that file quote behaves as the standard Racket quote.
Since +, *, -, / are bound to their standard Racket meaning,
the functions ⊕ ⊗ ⊖ ⊘ are used where the arguments are (automatically simplified) 
symbolic expressions.

For functions such as expt, sin etc. the corresponding functions that handle symbolic
expressions are Expt, Sin, etc.

Enjoy
/soegaard
