import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariantStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOverStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

theorem PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS hσ T hT
  have hG : Measurable fun π : Fin (e + 1) → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin (e + 1) → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hC : Measurable (fun p : (Fin (e + 1) → Fin n → ℂ) × EuclideanSpace ℂ (Fin (e + 1)) =>
      T (cntOver S p.1 p.2)) := hT.comp (GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hσ)
  have hF : Measurable (Function.uncurry fun (π : Fin (e + 1) → Fin n → ℂ)
      (w : EuclideanSpace ℂ (Fin (e + 1))) => matGauss π * T (cntOver S π w)) :=
    (hG.comp measurable_fst).mul hC
  have h1 : ∀ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1),
        matGauss π * T (cntOver S π w) := by
    intro π
    rw [lintegral_const_mul' _ _ (by unfold matGauss; exact ENNReal.ofReal_ne_top)]
  have h0 : ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)), w ≠ 0 := by
    rw [ae_iff]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  rw [lintegral_congr_ae ((ae_restrict_of_ae h0).mono fun w hw => GlobalTheory.T.fibre_count_rotation_invariant n e S hS w hw T),
    setLIntegral_const, mul_comm]
