import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairing
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) → ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M', IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.detSpan_conj_mul_mem_range | exact GlobalTheory.detSpan_conj_mul_mem_range | (intros; apply GlobalTheory.detSpan_conj_mul_mem_range <;> assumption)
