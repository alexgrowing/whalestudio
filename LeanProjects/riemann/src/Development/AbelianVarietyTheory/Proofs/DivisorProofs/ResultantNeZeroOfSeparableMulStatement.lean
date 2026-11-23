import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul : ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable → resultant P Q ≠ 0 := by
  first | exact @GlobalTheory.resultant_ne_zero_of_separable_mul | exact GlobalTheory.resultant_ne_zero_of_separable_mul | (intros; apply GlobalTheory.resultant_ne_zero_of_separable_mul <;> assumption)
