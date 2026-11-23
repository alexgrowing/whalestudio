import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRadiusDelNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_radius_del_norm_bound : ∀ (ι : Type) [Fintype ι] (r : (ι → ℂ) → ℝ) (G : Matrix ι ι ℂ) (CP : ℝ) (z : ι → ℂ), ContDiffAt ℝ 2 r z → 0 < r z → G.PosSemidef → FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2)) (fun ξ η => CP * formOf G ξ η) → FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf G) → ∀ ξ : ι → ℂ, ‖del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ‖ ^ 2 ≤ 2 * Real.pi * |CP| * gnorm G ξ ^ 2 ∧ |(leviForm (fun x => Real.log (r x)) z ξ ξ).re| ≤ 2 * Real.pi * |CP| * gnorm G ξ ^ 2 := by
  first | exact @GlobalTheory.InterpCurv.del_log_sq_le_and_levi_log_le | exact GlobalTheory.InterpCurv.del_log_sq_le_and_levi_log_le | (intros; apply GlobalTheory.InterpCurv.del_log_sq_le_and_levi_log_le <;> assumption)
