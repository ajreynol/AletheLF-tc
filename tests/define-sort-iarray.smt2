
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-sort Array 2)
(declare-sort Int 0)
(define-sort IntArray (T) (Array Int T))
(declare-const a (Array Int Bool))
(declare-const b (IntArray Bool))
(define-fun P () Bool (= a b))
