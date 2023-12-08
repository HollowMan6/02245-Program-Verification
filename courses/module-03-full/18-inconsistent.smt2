(declare-const null Int)

; inconsistent axioms
(assert (= null 0))
(assert (= null 17))

; wrong statement
(assert (not
  (> 42 23)
))

(check-sat) ; unsat