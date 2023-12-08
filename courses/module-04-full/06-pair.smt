; domain Pair { ... }
(declare-sort Pair)

; function cons(a: Int, b: Int): Pair
(declare-fun cons (Int Int) Pair)

; function first(p: Pair): Int
(declare-fun first (Pair) Int)

; function second(p: Pair): Int
(declare-fun second (Pair) Int)

; axiom { forall a: Int, b:Int :: first(cons(a,b)) == a }
(assert (forall ((a Int) (b Int)) 
    (= a (first (cons a b)))
))

; axiom { forall a: Int, b:Int :: second(cons(a,b)) == b }
(assert (forall ((a Int) (b Int)) 
    (= b (second (cons a b)))
))

; !wp[var p: Pair; p := cons(1,2); assert second(p) > first(p)](true)
(assert (not
  (forall ((p Pair)) (> (second (cons 1 2)) (first (cons 1 2))))
))

(check-sat)