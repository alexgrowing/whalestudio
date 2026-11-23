import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvector
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerOperator_injective_eigenvector : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  first | exact @GlobalTheory.eulerOp_injective_eigen | exact GlobalTheory.eulerOp_injective_eigen | (intros; apply GlobalTheory.eulerOp_injective_eigen <;> assumption)
