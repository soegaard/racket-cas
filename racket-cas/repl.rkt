#lang racket
(require "racket-cas.rkt")
(provide (all-from-out "racket-cas.rkt"))

; the start submodule redefines ' and ` to provide automatic simplification
(require (submod "racket-cas.rkt" start))

(displayln "Welcome to Racket CAS.")
(displayln "Use ' and ` to create symbolic expressions.")
(displayln "Expressions produced by ' and ` are automatically simplified.")
(displayln "Call  normalize  to run the automatic simplifier on a non-simplified expression.")
(newline)
(displayln "Write Jens Axel Søgaard (jensaxel@soegaard.net) with questions, bugs etc.")           
(newline)
(displayln "/soegaard")
(newline)



