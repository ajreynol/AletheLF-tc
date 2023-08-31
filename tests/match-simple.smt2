
(declare-const => (-> Bool Bool Bool))

(declare-sort Int 0)
(declare-consts <numeral> Int)

(declare-type Pair (Type Type))
(declare-const pair (-> (! Type :var U :implicit) (! Type :var T :implicit) U T (Pair U T)))
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const + (-> Int Int Int) :right-assoc)
(declare-const < (-> Int Int Bool) :right-assoc)

; `rm_from_sum s t`
; `rm_from_sum a (+ a b)` = (pair b true)
; `rm_from_sum a (+ c b)` = (pair (+ c b) false)
; 
(program rm_from_sum ((x Int) (y Int) (z Int))
  (Int Int) (Pair Int Bool)
  (
    ((rm_from_sum x (+ y z))
      (alf.match ((w Int) (b Bool))
        ; head
        (rm_from_sum x z)
        ; matches (pair w b)
        ((pair w b) (alf.ite 
                      (alf.is_eq x y) 
                      (pair w true) 
                      (pair (+ y w) b)))
      ))
    ((rm_from_sum x y) (pair y false))
  )
)

(declare-rule rm_sum ((x Int) (y Int))
  :args (x y)
  :conclusion (=> (< 0 x)
                (alf.match ((w Int) (b Bool))
                  (rm_from_sum x y) ; head
                  ((pair w b) (alf.ite b (< w y) (= w y)))))
)

(declare-const a Int)
(declare-const b Int)
(step @p0 (=> (< 0 a) (< b (+ a b))) :rule rm_sum :args (a (+ a b)))
