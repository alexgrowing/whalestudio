import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlRepresentativesRightMulPerm
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUlRepresentatives_right_mul_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l), ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulFam_perm | exact GlobalTheory.HeckeFamilyMatrices.ulFam_perm | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulFam_perm <;> assumption)
