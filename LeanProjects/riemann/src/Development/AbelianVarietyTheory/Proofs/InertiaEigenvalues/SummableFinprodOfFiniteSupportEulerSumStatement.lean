import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableFinprodOfFiniteSupportEulerSum
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_finprod_of_finite_support_euler_sum : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (a : ∀ v, X v → ℝ) (s : ι → ℝ), (∀ v x, 0 ≤ a v x) → (∀ v, a v (x0 v) = 1) → Summable s → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, a v x ≤ s v) → Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ∏ᶠ v, a v (f.1 v)) := by
  first | exact @GlobalTheory.summable_finprod_of_finite_support_euler | exact GlobalTheory.summable_finprod_of_finite_support_euler | (intros; apply GlobalTheory.summable_finprod_of_finite_support_euler <;> assumption)
