import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastMemDifferentIdealPowLe
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧ (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by
  first | exact @GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | exact GlobalTheory.exists_natCast_mem_differentIdeal_pow_le | (intros; apply GlobalTheory.exists_natCast_mem_differentIdeal_pow_le <;> assumption)
