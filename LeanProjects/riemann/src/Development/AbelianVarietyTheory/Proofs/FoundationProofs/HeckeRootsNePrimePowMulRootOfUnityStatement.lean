import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  first | exact @GlobalTheory.FactorsAtL.factors_ne_zero | exact GlobalTheory.FactorsAtL.factors_ne_zero | (intros; apply GlobalTheory.FactorsAtL.factors_ne_zero <;> assumption)
