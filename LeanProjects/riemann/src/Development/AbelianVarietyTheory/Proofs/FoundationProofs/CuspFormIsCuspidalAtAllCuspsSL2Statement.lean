import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll <;> assumption)
