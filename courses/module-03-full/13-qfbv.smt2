; SMT solvers also support bitvector arithmetic for fixed sizes
; this corresponds to arithmetic performed on actual computers.
; For example, we can use SMT for "superoptimizations", that is,
; finding the shortest possible (assembly) code for some expression.
; 
; As a concrete example, assume we are given the expression
; (x & y) * (-2) + (y + x),
; where & is bitwise conjunction and x and y are numbers stored in
; 32-bit integers.
; We might guess that (xor x y) is a much shorter, yet equivalent, 
; expression. We can use the bitvector theory to check this.

(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))

(assert
    (not
        (=
            (bvxor x y)
            (bvadd (bvmul (bvand x y) #xFFFFFFFE) (bvadd y x))
        )
    )
)
(check-sat)
(echo "unsat means both expressions are equivalent")