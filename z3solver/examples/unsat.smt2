; Unsatisfiable example: contradictory constraints
(set-option :produce-unsat-cores true)
(declare-const x Int)
(assert (! (> x 10) :named x-greater-than-10))
(assert (! (< x 5) :named x-less-than-5))
(check-sat)
