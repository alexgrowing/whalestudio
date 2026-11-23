import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartEqOneMulInvMemSplitCongruenceIdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finPart_eq_one_mul_inv_mem_split_congruence_ideles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  first | exact @GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem <;> assumption)
