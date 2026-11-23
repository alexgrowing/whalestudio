import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleIsUnitDetLocalInvolution
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_isUnit_det_local_involution : ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.LocalLift.exists_admissible_isUnit_det | exact GlobalTheory.LocalLift.exists_admissible_isUnit_det | (intros; apply GlobalTheory.LocalLift.exists_admissible_isUnit_det <;> assumption)
