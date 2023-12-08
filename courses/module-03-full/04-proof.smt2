; Solving the SAT problem means finding an assignment that makes a formula true.
; How can we use it to *prove* a law of propositional logic?

(declare-const x Bool)
(declare-const y Bool)

(push)
(echo "De Morgan's law: !(x && y) == (!x || !y)")
(assert 
    (= 
        (not (and x y) )
        (or (not x) (not y))
    )
)
(check-sat)
(echo "What does this tell us?")
; it's possible that De Morgan's law sometimes holds. It's not a proof!
(pop)

(push)
(echo "Can we prove De Morgan's law? I.e., !(x && y) == (!x || !y)")
; idea: Try to find a model that makes the *negation* true. If we can find such a model,
;       then there is a *counterexample*, disproving the law. If no such model exists,
;       then the law must hold for *all* interpretations of the variables.
(assert 
    (not ; look for models that invalidate the law
        (=
            (not (and x y) )
            (or (not x) (not y))
        )
    )
)
(check-sat)
(echo "What does this tell us?")
(echo "There is no counterexample disproving De Morgan's law. Hence, it must be true")
(echo "Notice that, for proving properties, our goal is to end up with unsat.")
(pop)

(push)
(echo "What if we try to prove a wrong law, say !(x && y) == (!x && !y)")
(assert 
    (not ; look for models that invalidate the law
        (=
            (not (and x y) )
            (and (not x) (not y))
        )
    )
)
(check-sat)
(get-model)
(echo "We get a concrete model that tells us how to violate the proposed law.")
(pop)

; SUMMARY: 
; To use SAT solvers for proving properties that should hold for all possible interpretations of variables, we need to look for the absence of counterexamples.
; That is, we aim to prove that the negation of the property is unsatisfiable. 