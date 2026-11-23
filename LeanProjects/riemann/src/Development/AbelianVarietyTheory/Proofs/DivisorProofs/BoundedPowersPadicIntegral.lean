import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilOrbitalMeasure
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_powers_padic_integral : ∀ (M : Type) [CommRing M] [Algebra ℚ M] (q : ℕ) [Fact q.Prime] (ι : Type) [Fintype ι] (f : M →ₗ[ℚ] (ι → ℚ)), Function.Injective f → ∀ (a : M) (B : ℝ), (∀ (k : ℕ) (i : ι), ‖((f (a ^ k) i : ℚ) : ℚ_[q])‖ ≤ B) → ∀ τ : M →+* PadicAlgCl q, ‖τ a‖ ≤ 1 := by
  first | (exact @GlobalTheory.norm_conj_le_one_of_bounded_coords) | (exact GlobalTheory.norm_conj_le_one_of_bounded_coords) | (intros; apply GlobalTheory.norm_conj_le_one_of_bounded_coords <;> assumption)
