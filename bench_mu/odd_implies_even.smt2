(declare-fun G (Int) Bool)
(declare-fun NotEven (Int) Bool)
(declare-fun NotOdd (Int) Bool)
(declare-fun Odd (Int) Bool)
(declare-fun Even (Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int)) (G x)))

(assert (forall ((x Int))
  (= (G x) (or (Even (+ x 1)) (NotOdd x)))))

(assert (and nu (forall ((x Int))
  (= (NotEven x) (and (not (= x 0)) (NotOdd (- x 1)))))))

(assert (and nu (forall ((x Int))
  (= (NotOdd x) (NotEven (- x 1))))))

(assert (and mu (forall ((x Int))
  (= (Even x) (or (= x 0) (Odd (- x 1)))))))

(assert (and mu (forall ((x Int))
  (= (Odd x) (Even (- x 1))))))

(check-sat)
