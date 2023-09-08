(include "../proofs/rules/Cvc5.smt2")
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(declare-fun p1 () Bool)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun a () U)
(declare-fun b () U)
(define-fun @t1 () Bool (= a b))
(define-fun @t2 () Bool (= c d))
(define-fun @t3 () Bool (and p1 true))
(define-fun @t4 () Bool (and p2 p3))
(define-fun @t5 () Bool (= (f a c) (f b d)))
(define-fun @t6 () Bool (and @t1 @t2))
(assume @p1 @t1)
(assume @p2 @t2)
(assume @p3 @t3)
(assume @p4 (or (not p1) @t4))
(assume @p5 (or (not p3) (not @t5)))
; WARNING: add trust step for THEORY_REWRITE
; trust THEORY_REWRITE
(step @p6 :rule trust :args ((= @t3 p1)))
(step @p7 :rule eq_resolve :premises (@p3 @p6))
(step @p8 :rule chain_resolution :premises (@p4 @p7) :args ((and false p1)))
(step @p9 :rule cnf_and_pos :args (@t4 1))
(step @p10 :rule reordering :premises (@p9) :args ((or p3 (not @t4))))
(step @p11 :rule chain_resolution :premises (@p10 @p8) :args ((and false @t4)))
(step @p12 :rule chain_resolution :premises (@p5 @p11) :args ((and false p3)))
(assume-push @p13 @t1)
(assume-push @p14 @t2)
(step @p15 :rule refl :args (f))
(step @p16 :rule ho_cong :premises (@p15 @p1))
(step @p17 :rule ho_cong :premises (@p16 @p2))
(step-pop @p18 :rule scope :premises (@p17))
(step-pop @p19 :rule scope :premises (@p18))
(step @p20 :rule process_scope :premises (@p19) :args (@t5))
(step @p21 :rule implies_elim :premises (@p20))
(step @p22 :rule cnf_and_neg :args (@t6))
(step @p23 :rule resolution :premises (@p22 @p21) :args (true @t6))
(step @p24 :rule reordering :premises (@p23) :args ((or @t5 (not @t1) (not @t2))))
(step @p25 :rule chain_resolution :premises (@p24 @p12 @p2 @p1) :args ((and true @t5 false @t2 false @t1)))

