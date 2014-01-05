racket-cas
==========

A Simple Computer Algebra System (CAS) for Racket
-------------------------------------------------

Here is a short example. Open racket-cas.rkt in DrRacket and run it.

To begin write:
    > (require (submod "." start))
This changes the meaning of quote such that quoted expression are
normalized automatically.
    > '(+ x 2 a 3 (* 4 x))
    '(+ 5 a (* 5 x))

Let jump to something useful. The Taylor series of sin(x) around x=2
of degree 3:
    > (taylor '(sin x) x 2 3)
    '(+ (* -1/2 (expt (+ -2 x) 2) (sin 2)) (* -1/6 (expt (+ -2 x) 3)
(cos 2)) (* (+ -2 x) (cos 2)) (sin 2))

Since (sin 2) can not be represented exactly it is not evaluated
numerically. We can use N:
    > (expand (N (taylor '(sin x) x 2 3)))
    '(+  -0.6318662024609201
       (* 2.2347416901985055         x)
      (* -0.8707955499599832 (expt x 2))
      (* 0.0693578060911904  (expt x 3)))

Switching expand and N ought to have worked, but it currently provokes
an infinite loop.

We can substitute 2.1 for x first and the evaluate numerically:
    > (subst (expand (N (taylor '(sin x) x 2 3))) x 2.1)
    0.8632056138429305
For a comparision:
    > (sin 2.1)
    0.8632093666488738

We can also evaluate using bigfloats:
    > (bf-N (taylor '(sin x) x 2 3) 100 x (bf 2.1))
    (bf #e0.86320561384293019376447471077597)

We can also compute (some) limits:
    > (limit '(/ (sin x) x) x 0)
   1

Note: In the code quote is the standard quote.
In order to have automatic simplification ⊕ ⊗ ⊖ ⊘ is used in place of
+ * - and /.
For other functions capitalization is used That is Expt, Sin, ...
accepts expressions as arguments.