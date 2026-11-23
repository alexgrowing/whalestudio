import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicJacobianEqZeroPoincareGro
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) → (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) → IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧ ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare | exact GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare | (intros; apply GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare <;> assumption)
