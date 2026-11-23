import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvChar
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧ (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  first | exact @GlobalTheory.EisM.ConjForm.conj_form | exact GlobalTheory.EisM.ConjForm.conj_form | (intros; apply GlobalTheory.EisM.ConjForm.conj_form <;> assumption)
