; Exercise: Placement of wedding guests
; We have to assign chairs to three guests, called Alice, Bob, and Charlie
; There are three chairs in a row, called Left, Middle, and Right
; Alice does not want to sit on the leftmost chair
; Alice does not want to sit next to Charlie
; Bob does not want to sit to the right of Charlie
; Is it possible to assign our guests such that they are all happy?

; We introduce a variable XY to indicate that guest X sits in chair Y
(declare-const AL Bool)
(declare-const AM Bool)
(declare-const AR Bool)
(declare-const BL Bool)
(declare-const BM Bool)
(declare-const BR Bool)
(declare-const CL Bool)
(declare-const CM Bool)
(declare-const CR Bool)

; Alice does not want to sit on the leftmost chair
(assert (not AL))

; Alice does not want to sit next to Charlie
(assert 
    (and
        (=> (or AL AR) (not CM))
        (=> AM (and (not CL) (not CR)))
    )
)

; Bob does not want to sit to the right of Charlie
(assert
    (and
        (=> CL (not BM))
        (=> CM (not BR))
    )
)

(check-sat)
(get-model)
(echo "All 3 constraints. What's wrong here?")

(push)
; each person gets a chair
(assert (or AL AM AR))
(assert (or BL BM BR))
(assert (or CL CM CR))
(check-sat)
(get-model)
(echo "Everyone gets a chair. What's wrong here?")

(push)
; every person gets at most one chair
(assert 
    (and
        (=> AL (not AM))
        (=> AL (not AR))
        (=> AM (not AR))
        (=> BL (not BM))
        (=> BL (not BR))
        (=> BM (not BR))
        (=> CL (not CM))
        (=> CL (not CR))
        (=> CM (not CR))
    )
)
(check-sat)
(get-model)
(echo "Everyone gets at most one chair. What's wrong here?")

(push)
; every chair gets at most one person
(assert 
    (and
        (=> AL (not BL))
        (=> AL (not CL))
        (=> BL (not CL))
        (=> AM (not BM))
        (=> AM (not CM))
        (=> BM (not CM))
        (=> AR (not CR))
        (=> AR (not BR))
        (=> BR (not CR))
    )
)
(echo "Every chair gets at most one person.")
(check-sat)
(echo "We cannot make everyone happy.")
; we could let Alice take the leftmost chair to partially fix this

(pop)
(pop)
(pop)


