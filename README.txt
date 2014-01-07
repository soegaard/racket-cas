racket-cas
==========

A Simple Computer Algebra System (CAS) for Racket
-------------------------------------------------

Here is a short example. Open racket-cas.rkt in DrRacket and run it.

To begin write:
    > (require (submod "." start))
This changes the meaning of quote such that quoted expressions are
normalized automatically.
    > '(+ x 2 a 3 (* 4 x))
    '(+ 5 a (* 5 x))

Let's jump to something useful. The Taylor series of sin(x) around x=2
of degree 3:
    > (taylor '(sin x) x 2 3)
    '(+ (* -1/2 (expt (+ -2 x) 2) (sin 2)) (* -1/6 (expt (+ -2 x) 3)
(cos 2)) (* (+ -2 x) (cos 2)) (sin 2))

Since (sin 2) can not be represented exactly it is not evaluated
numerically. We can use N that forces numeric computation:
    > (N (expand (taylor '(sin x) x 2 3)))
    '(+  -0.6318662024609201
       (* 2.2347416901985055         x)
      (* -0.8707955499599832 (expt x 2))
      (* 0.0693578060911904  (expt x 3)))
Or simpler use 2.0 instead of 2, since inexact numbers are contagious: 
   > (expand (taylor '(sin x) x 2.0 3))
   <same result>

We can substitute 2.1 for x first and the evaluate numerically:
    > (subst (expand (N (taylor '(sin x) x 2 3))) x 2.1)
    0.8632056138429305
For comparision:
    > (sin 2.1)
    0.8632093666488738

We can also evaluate using bigfloats:
    > (bf-N (taylor '(sin x) x 2 3) 100 x (bf 2.1))
    (bf #e0.86320561384293019376447471077597)

Let's draw some graphs illustrating approximation by Taylor polynomials.
    > (require plot)
    > (plot (list (function (compile (taylor '(sin x) x 0 5)) #:color "green")
              (function sin #:color "red" -3.14 3.14)))
    <nice graphs appear in DrRacket>

Let's compare Taylor polynomials of various orders.
    > (plot (append (for/list ([n 6]) (function (compile (taylor '(cos x) x pi n)) #:color (+ n 1)))
                    (list (function cos #:color "red")))
            #:x-min (- pi) #:x-max (* 3 pi) #:y-min -2 #:y-max 2)
     <graphs appear>

We can also compute (some) limits:
    > (limit '(/ (sin x) x) x 0)
   1

Note: In the code quote is the standard quote.
In order to have automatic simplification ⊕ ⊗ ⊖ ⊘ is used in place of
+ * - and /.
For other functions capitalization is used That is Expt, Sin, ...
accepts expressions as arguments.