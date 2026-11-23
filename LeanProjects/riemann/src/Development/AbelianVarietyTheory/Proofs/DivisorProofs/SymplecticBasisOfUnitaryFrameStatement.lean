import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBasisOfUnitaryFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_basis_of_unitary_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E),
    (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 → IsFrameU σ J x y →
    ∃ (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
      (blk : Fin q → Finset (Fin n × Fin d)),
      (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) ∧
      (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) := by
  first | exact @GlobalTheory.ThKTorus.exists_frame_symplectic_basis | exact GlobalTheory.ThKTorus.exists_frame_symplectic_basis | (intros; apply GlobalTheory.ThKTorus.exists_frame_symplectic_basis <;> assumption)
