; Simple example: find x and y such that x > 0, y > 0, and x + y < 10
(set-option :produce-unsat-cores true)
(declare-const x Int)
(declare-const y Int)
(assert (! (> x 0) :named x-positive))
(assert (! (> y 0) :named y-positive))
(assert (! (< (+ x y) 10) :named sum-less-than-10))
(check-sat)
