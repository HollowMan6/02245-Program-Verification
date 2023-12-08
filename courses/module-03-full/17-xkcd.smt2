; applying SMT solvers to https://xkcd.com/287
; now with bitvectors

;display bitvector literals in decimal format
(set-option :pp.bv-literals false) 



(declare-const fruit (_ BitVec 32))
(declare-const fries (_ BitVec 32))
(declare-const salad (_ BitVec 32))
(declare-const wings (_ BitVec 32))
(declare-const sticks (_ BitVec 32))
(declare-const plate (_ BitVec 32))

(assert
    (=
        (bvadd 
            (bvmul (_ bv215 32) fruit) 
            (bvmul (_ bv275 32) fries) 
            (bvmul (_ bv335 32) salad) 
            (bvmul (_ bv355 32) wings) 
            (bvmul (_ bv420 32) sticks) 
            (bvmul (_ bv580 32) plate)
        )
        (_ bv1505 32)
    )
)

(assert (bvsge fruit (_ bv0 32)))
(assert (bvsge fries (_ bv0 32)))
(assert (bvsge salad (_ bv0 32)))
(assert (bvsge wings (_ bv0 32)))
(assert (bvsge sticks (_ bv0 32)))
(assert (bvsge plate (_ bv0 32)))

; try bv25 instead of 10
(assert (and
    (bvsle fruit (_ bv10 32))
    (bvsle fries (_ bv10 32))
    (bvsle salad (_ bv10 32))
    (bvsle wings (_ bv10 32))
    (bvsle sticks (_ bv10 32))
    (bvsle plate (_ bv10 32))
))

(check-sat)
(get-model)