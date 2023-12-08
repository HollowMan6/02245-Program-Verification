; applying SMT solvers to https://xkcd.com/287
; finding all solutions by hand
(declare-const fruit Int)
(declare-const fries Int)
(declare-const salad Int)
(declare-const wings Int)
(declare-const sticks Int)
(declare-const plate Int)

(assert
    (=
        (+ 
            (* 215 fruit) 
            (* 275 fries) 
            (* 335 salad) 
            (* 355 wings) 
            (* 420 sticks) 
            (* 580 plate)
        )
        1505
    )
)

(assert (and 
    (>= fruit 0)
    (>= fries 0)
    (>= salad 0)
    (>= wings 0)
    (>= sticks 0)
    (>= plate 0)
))

(check-sat)
(get-model)

(assert (or 
    (not (= fruit 7)) 
    (not (= fries 0)) 
    (not (= salad 0)) 
    (not (= wings 0)) 
    (not (= sticks 0)) 
    (not (= plate 0))
))

(check-sat)
(get-model)

(assert (or 
    (not (= fruit 1)) 
    (not (= fries 0)) 
    (not (= salad 0)) 
    (not (= wings 2)) 
    (not (= sticks 0)) 
    (not (= plate 1))
))

(check-sat) ; unsat means there are no other solutions