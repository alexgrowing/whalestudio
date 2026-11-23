import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTqRepresentatives_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime → tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  first | exact @GlobalTheory.tqFam_cosets_distinct | exact GlobalTheory.tqFam_cosets_distinct | (intros; apply GlobalTheory.tqFam_cosets_distinct <;> assumption)
