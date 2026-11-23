import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  first | exact @GlobalTheory.EisM.coef_qs | exact GlobalTheory.EisM.coef_qs | (intros; apply GlobalTheory.EisM.coef_qs <;> assumption)
