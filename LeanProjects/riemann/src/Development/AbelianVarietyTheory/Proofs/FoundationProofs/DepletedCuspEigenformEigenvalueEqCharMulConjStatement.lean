import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConj
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  first | exact @GlobalTheory.EisMReal.eig_conj | exact GlobalTheory.EisMReal.eig_conj | (intros; apply GlobalTheory.EisMReal.eig_conj <;> assumption)
