import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansion
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a → PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  first | exact @GlobalTheory.EisM.Vo_polyB_qs | exact GlobalTheory.EisM.Vo_polyB_qs | (intros; apply GlobalTheory.EisM.Vo_polyB_qs <;> assumption)
