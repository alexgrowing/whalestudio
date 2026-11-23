import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartz
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  first | exact @GlobalTheory.Unf.PartialClass.smooth_schwartz | exact GlobalTheory.Unf.PartialClass.smooth_schwartz | (intros; apply GlobalTheory.Unf.PartialClass.smooth_schwartz <;> assumption)
