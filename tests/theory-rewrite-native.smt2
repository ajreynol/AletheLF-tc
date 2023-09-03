(declare-type Theory ())
(declare-const THEORY_BUILTIN Theory)
(declare-const THEORY_BOOL Theory)
(declare-const THEORY_UF Theory)
(declare-const THEORY_ARITH Theory)
(declare-const THEORY_BV Theory)
(declare-const THEORY_FF Theory)
(declare-const THEORY_FP Theory)
(declare-const THEORY_ARRAYS Theory)
(declare-const THEORY_DATATYPES Theory)
(declare-const THEORY_SEP Theory)
(declare-const THEORY_SETS Theory)
(declare-const THEORY_BAGS Theory)
(declare-const THEORY_STRINGS Theory)
(declare-const THEORY_QUANTIFIERS Theory)

(declare-type Method ())
(declare-const RW_REWRITE Method)
(declare-const RW_EXT_REWRITE Method)
(declare-const RW_REWRITE_EQ_EXT Method)
(declare-const RW_EVALUATE Method)
(declare-const RW_REWRITE_THEORY_PRE Method)
(declare-const RW_REWRITE_THEORY_POST Method)
(declare-const SB_DEFAULT Method)
(declare-const SB_LITERAL Method)
(declare-const SB_FORMULA Method)
(declare-const SBA_SEQUENTIAL Method)
(declare-const SBA_SIMUL Method)
(declare-const SBA_FIXPOINT Method)

(declare-rule theory_rewrite ((T Type) (F T) (theory Theory) (method Method))
    :args (F theory method)
    :conclusion F
)
