import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubGoodIdempotentEqBadTupleSums
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums : ∀ (D : D7), ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ 1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  first | exact @GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | exact GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | (intros; apply GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums <;> assumption)
