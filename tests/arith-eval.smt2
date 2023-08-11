(declare-sort Int 0)
(declare-sort Real 0)

(declare-consts <numeral> Int)
(declare-consts <decimal> Real)


(declare-const = (-> (! Type :var T :implicit) T T Bool))

(program a.typeunion ()
    (Type Type) Type
    (
      ((a.typeunion Int Int) Int)
      ((a.typeunion Int Real) Real)
      ((a.typeunion Real Int) Real)
      ((a.typeunion Real Real) Real)
    )
)

(declare-const + (-> (! Type :var T :implicit) 
                     (! Type :var U :implicit) 
                     T U (a.typeunion T U)))
(declare-const - (-> (! Type :var T :implicit) 
                     (! Type :var U :implicit) 
                     T U (a.typeunion T U)))
(declare-const < (-> (! Type :var T :implicit) 
                      T T Bool))
(declare-const <= (-> (! Type :var T :implicit) 
                      T T Bool))


(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((run_evaluate (= a b))  (eval.is_eq (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (< a b))  (eval.is_neg (run_evaluate (- a b))))
      ((run_evaluate (<= a b)) (let ((x (run_evaluate (- a b)))) 
                                 (eval.or (eval.is_neg x) (eval.is_zero x))))
      ((run_evaluate (+ a b))  (eval.add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b))  (eval.add (run_evaluate a) (eval.neg (run_evaluate b))))
      ((run_evaluate z)        z)
    )
)

(declare-rule eval
   ((T Type) (U Type) (a T) (b U))
   :premises ()
   :args (a b)
   :requires (((run_evaluate a) (run_evaluate b)))
   :conclusion (= a b)
)

