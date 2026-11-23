import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApply
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  first | exact @GlobalTheory.slices_test' | exact GlobalTheory.slices_test' | (intros; apply GlobalTheory.slices_test' <;> assumption)
