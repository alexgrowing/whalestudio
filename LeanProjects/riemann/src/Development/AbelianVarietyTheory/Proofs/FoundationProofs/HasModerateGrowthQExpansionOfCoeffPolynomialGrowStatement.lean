import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrow
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  first | exact @GlobalTheory.EisM.mod_qs_of_polyB | exact GlobalTheory.EisM.mod_qs_of_polyB | (intros; apply GlobalTheory.EisM.mod_qs_of_polyB <;> assumption)
