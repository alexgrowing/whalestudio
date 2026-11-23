import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedMetricCurvatureBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolated_metric_curvature_bound : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {Cμ C₀ C₂ C₃ K : ℝ} {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r s : (ι → ℂ) → ℝ} {G : (ι → ℂ) → Matrix ι ι ℂ}, IsPosFrame U H₀ → IsPosFrame U H → (∀ z ∈ U, 1 < r z) → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, (G z).PosSemidef) → PowComparable U r Cμ H₀ H → OneFormBound U H₀ G (fun z ξ => conn H z ξ - conn H₀ z ξ) C₂ → TwoFormBound U H G (curv H) C₃ → TwoFormBound U H₀ G (curv H₀) C₀ → (0 ≤ Cμ → WeightBound K Cμ U r s G) → TwoFormBound U (interp H₀ H s) G (curv (interp H₀ H s)) (2 * (|C₀| + |C₃| + 2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2)) := by
  first | exact @GlobalTheory.InterpCurvBound.interp_curv_bound | exact GlobalTheory.InterpCurvBound.interp_curv_bound | (intros; apply GlobalTheory.InterpCurvBound.interp_curv_bound <;> assumption)
