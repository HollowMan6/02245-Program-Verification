; preamble with all declarations

(declare-sort Color) 

(declare-const Black Color) 
(declare-const White Color) 
(declare-const Red Color)
(declare-const Green Color)
(declare-const Blue Color)
(declare-const Yellow Color)

(declare-fun isInDanishFlag ((Color)) Bool)
(declare-fun mix (Color Color) Color)

(declare-const x Color)

; --------------------------------------------------------------
; background predicate: assert all axioms

; axiom stating that all constructors yield different colors
(assert (distinct Black White Red Green Blue Yellow))

; axiom stating that there are no other colors
(assert 
    (forall ((a Color)) 
        (or
            (= a Black)
            (= a White)
            (= a Red)
            (= a Green)
            (= a Blue)
            (= a Yellow)
        )
    )
)

; axiom for danish flag
(assert 
    (forall ((a Color))
        (= 
            (isInDanishFlag a) 
            (or
                (= a Red)
                (= a White)
            )
        )
    )
)

; axioms for fixed colors
(assert (= (mix Red Green) Yellow))
(assert (= (mix Blue Yellow) White))

; axiom stating mixing colors is symmetric
(assert 
    (forall ((a Color) (b Color))
        (= (mix a b) (mix b a))
    )
)

; axioms for black
(assert 
    (forall ((a Color) (b Color))
        (and
            (=> (= a Black) (= Black (mix a b)))
        )
    )
)

; --------------------------------------------------------------
; precondition

(assert (= x Red))

; --------------------------------------------------------------
; !WP(S, Q)

(assert 
    (not
        (isInDanishFlag (mix Blue (mix x Green)))
    )
)

(check-sat)