import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence : ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) → ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  first | exact @GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | exact GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | (intros; apply GlobalTheory.roots_norm_le_of_bounded_two_step_recursion <;> assumption)
