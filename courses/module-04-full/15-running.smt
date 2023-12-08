; the failing example using standard ewp and labels for assignment;
; the label here is given by the attribute (! ASSERTION :label)
(set-option :produce-assignments true) ; needed for supporting labels

(declare-const x0 Int)
(declare-const y0 Int)
(declare-const z0 Int)
(declare-const z1 Int)
(declare-const z2 Int)
(declare-const A Bool)

(assert
    (not ; for checking validity
        (=>
            (and (>= x0 0) (>= y0 0))
            (=>
                (= z0 (- x0 y0))
                (=>
                    (= 
                        A
                        (and
                            (!  ; *not* a negation, needed to add :named attribute
                                (= z2 (* 3 x0))
                                :named L6 ; here we add a label that should be set to false iff this assertion fails
                            )
                            true
                        )
                    )
                    (and
                        (=> 
                            (< z0 0)
                            (=>
                                (= z1 (+ z0 y0))
                                (=> (= z2 (+ z1 (* 2 x0))) A)
                            )
                        )
                        (=>
                            (not (< z0 0))
                            (=>
                                (= z1 (- z0 x0))
                                (=> (= z2 (+ z1 (* 4 y0))) A)
                            )
                        )
                    )
                )
            )
        )
    )
)
(echo "sat means verification fails; L6 = false iff assertion corresponding to the postcondition in line 6 (original program) fails.")
(check-sat)
(get-assignment)