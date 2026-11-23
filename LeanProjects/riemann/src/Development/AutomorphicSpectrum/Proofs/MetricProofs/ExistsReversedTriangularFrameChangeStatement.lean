import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChange
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reversed_triangular_frame_change : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ), IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) → (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 → (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm → ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧ (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧ R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  first | exact @GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | exact GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | (intros; apply GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame <;> assumption)
