(include "../programs/Utils.smt2")

; Bool is builtin
;(declare-type Bool ())

(declare-const ite (-> (! Type :var A :implicit) Bool A A A))
(declare-const not (-> Bool Bool))

(declare-const or (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U))
   :right-assoc-nil
)
(declare-const and (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U))
   :right-assoc-nil
)
(declare-const => (-> Bool Bool Bool)
   :right-assoc
)
(declare-const xor (-> Bool Bool Bool)
   :left-assoc
)

(declare-const = (-> (! Type :var A :implicit) A A Bool)
   :chainable and
)

(declare-const forall (-> (! Type :var A :implicit) A Bool Bool))

(declare-const exists (-> (! Type :var A :implicit) A Bool Bool))

(declare-const lambda (-> (! Type :var A :implicit) (! Type :var B :implicit) A B (-> A B)))

(declare-const distinct (-> (! Type :var A :implicit) A A Bool) :pairwise and)

;;;;;;;;;;;;;;;;;;

(declare-const skolem (-> (! Type :var A :implicit) A A))

; We construct all skolems by wrapping them in an application of `skolem`.
; The argument is either
; (1) an application of an internal function symbol @k.ID where ID is the
; skolem function id,
; (2) a term t, in the case of purify skolems, where t is the term.

; For example, the array diff skolem for arrays A and B is:
;   (skolem (@k.ARRAY_DIFF A B))
; where we have:
;   (declare-const @k.ARRAY_DIFF
;      (-> (! Type :var T :implicit) (! Type :var U :implicit) (Array T U) (Array T U) T))



; generic variables
; NOTE: does not check that U is a numeral
(declare-const const (-> (! Type :var U :implicit) U (! Type :var T) T))
