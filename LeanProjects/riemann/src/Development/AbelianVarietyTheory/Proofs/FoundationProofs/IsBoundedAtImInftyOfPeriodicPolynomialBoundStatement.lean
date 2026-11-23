import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsBoundedAtImInftyOfPeriodicPolynomialBound
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedAtImInfty_of_periodic_polynomial_bound : ∀ (f : ℍ → ℂ) (h : ℕ) (C : ℝ) (A : ℕ), 0 < h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((h : ℝ) +ᵥ τ) = f τ) → (∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ h → ‖f τ‖ ≤ C * τ.im ^ A) → IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound | exact GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound | (intros; apply GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound <;> assumption)
