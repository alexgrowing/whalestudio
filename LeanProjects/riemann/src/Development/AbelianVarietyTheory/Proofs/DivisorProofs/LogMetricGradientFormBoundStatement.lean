import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricGradientFormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_metric_gradient_form_bound : ∀ (Cμ CP κ : ℝ) (χ : ℝ → ℝ), 2 * Cμ + 2 < κ → IsCutoff χ → ∃ K : ℝ, ∀ (ι : Type) [Fintype ι] (U : Set (ι → ℂ)) (r : (ι → ℂ) → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ), 0 ≤ Cμ → IsOpen U → ContDiffOn ℝ ∞ r U → (∀ z ∈ U, Real.exp 1 ≤ r z) → (∀ z ∈ U, (G z).PosSemidef) → (∀ z ∈ U, FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2)) fun ξ η => CP * formOf (G z) ξ η) → (∀ z ∈ U, FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf (G z))) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ R : ℝ, 2 ≤ R → WeightBound K Cμ U r (fun z => t * cutWeight χ κ R r z) G := by
  first | exact @GlobalTheory.InterpCurv.weightBound_cutWeight | exact GlobalTheory.InterpCurv.weightBound_cutWeight | (intros; apply GlobalTheory.InterpCurv.weightBound_cutWeight <;> assumption)
