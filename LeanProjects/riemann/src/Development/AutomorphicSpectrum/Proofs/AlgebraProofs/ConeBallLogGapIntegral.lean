import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConeBallLogGapIntegral
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral : ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @ModelDimension.integral_coneBall_log_gap_eq | exact ModelDimension.integral_coneBall_log_gap_eq
