import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → Tz k r z' = Tz k r z ∧ (∃ m ∈ UH (Hb k), ∀ w, inWb k r w → g₀ *ᵥ w = mEmb k r m *ᵥ w) ∧ IsNormal0 k r hj β c⁻¹ z' z g₀⁻¹ ∧ 0 < Dj k r hj z z' g₀ ∧ Dj k r hj z' z g₀⁻¹ = Dj k r hj z z' g₀ ∧ (∀ l : Fin (r + 2), ‖Dmin k r z' z g₀⁻¹ l‖ = ‖Dmin k r z z' g₀ l‖) ∧ ∀ w, w ∈ Hcom k r z z' g₀ ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0 := by
  first | exact @GlobalTheory.Amp.NfMid.normal0_middle | exact GlobalTheory.Amp.NfMid.normal0_middle | (intros; apply GlobalTheory.Amp.NfMid.normal0_middle <;> assumption)
