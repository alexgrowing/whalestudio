import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariant
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_count_rotation_invariant : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
  ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
      ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver <;> assumption)
