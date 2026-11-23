import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBound
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_similitude_entry_sq_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  first | (exact @GlobalTheory.herm_scale_entry_bound) | (exact GlobalTheory.herm_scale_entry_bound) | (intros; apply GlobalTheory.herm_scale_entry_bound  <;> assumption)
