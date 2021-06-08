;; Original file: sum4.smt2
(set-logic HORN)
(declare-fun P0 (Int) Bool)
(declare-fun P1 (Int Int) Bool)
(declare-fun f (Int) Bool)

					;(assert (forall ((x1 Int) (x0 Int)) (=> (and (P0 x1) (= x0 0) (<= x1 0)) (P1 x1 x0))))
(assert (forall ((x1 Int) (x0 Int)) (=> (and (P0 x1) (f x0) (<= x1 0)) (P1 x1 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (P0 x1) (>= x1 1) (= x1 (+ 1 x0))) (P0 x0))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int) (x3 Int)) (=> (and (P0 x1) (P1 x2 x3) (>= x1 1) (= x1 (+ 1 x2)) (= x0 (+ x1 x3))) (P1 x1 x0))))
(assert (forall ((x2 Int) (x0 Int) (x1 Int)) (=> (and (= (* 4 x2) (+ 6 x0)) (= x1 (* 4 x2))) (P0 x2))))
(assert (forall ((x0 Int) (x3 Int) (x2 Int) (x1 Int)) (=> (and (P1 x2 x3) (>= x0 (+ 1 x3)) (= (* 4 x2) (+ 6 x0)) (= x1 (* 4 x2))) false)))
(check-sat)
