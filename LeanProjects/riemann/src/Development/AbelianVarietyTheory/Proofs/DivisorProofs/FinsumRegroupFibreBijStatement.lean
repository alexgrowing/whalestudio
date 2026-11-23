import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBij
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij : ∀ {α ι : Type} {κ : ι → Type} (U : α → ℂ) (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i), (Function.support U).Finite → (∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a) → (∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a') → (∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) → ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  first | (exact @GlobalTheory.finsum_regroup_fibre_bij) | (exact GlobalTheory.finsum_regroup_fibre_bij) | (intros; apply GlobalTheory.finsum_regroup_fibre_bij  <;> assumption)
