import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStepRecursion_localEulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  first | exact @GlobalTheory.LocSer.twoStep_eulerFactors | exact GlobalTheory.LocSer.twoStep_eulerFactors | (intros; apply GlobalTheory.LocSer.twoStep_eulerFactors <;> assumption)
