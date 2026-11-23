import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix

namespace GlobalTheory.SA.TransvG

section Det

variable {K : Type} [CommRing K]

theorem det_fromBlocks_swap {n : Type} [Fintype n] [DecidableEq n] (P A B D : Matrix n n K) :
    (fromBlocks P A B D).det = (fromBlocks (-A) P (-D) B).det := by
  have h : fromBlocks (-A) P (-D) B = fromBlocks P A B D * (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 *
      fromBlocks 1 1 0 1 : Matrix (n ⊕ n) (n ⊕ n) K) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul]

theorem det_updateRow_last {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det = (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h : (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp
  simp [Fin.castSucc_ne_last, h, ← two_mul]

theorem det_fromBlocks_single {n : Type} [Fintype n] [DecidableEq n] (l : n) (X Y : Matrix n n K) (t s : K) :
    (fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y).det =
      X.det * Y.det - t * s * ((X.updateRow l (Pi.single l 1)).det * (Y.updateRow l (Pi.single l 1)).det) := by
  have e1 : fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y =
      (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y (Sum.inl l) +
          t • Pi.single (Sum.inr l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e2 : (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (Pi.single (Sum.inr l) 1) =
      (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y (Sum.inr l) +
          s • Pi.single (Sum.inl l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e3 : (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1) =
      (fromBlocks (X.updateRow l (Pi.single l 1)) 0 0 (Y.updateRow l (Pi.single l 1))).submatrix
        (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb, @eq_comm _ l b]
  have e4 : (X.updateRow l 0).det = 0 := det_eq_zero_of_row_eq_zero l fun j => by simp
  rw [e1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₁₂, e2,
    det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₂₁, e3, det_permute,
    det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), e4]
  simp
  ring

theorem det_fromBlocks_last {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) A B
      (diagonal fun a => if a = Fin.last r then -T' else 0)).det =
      (-1) ^ (r + 1) * (A.det * B.det - T * T' *
        ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have h : (-diagonal fun a => if a = Fin.last r then -T' else 0) =
      diagonal fun a => if a = Fin.last r then T' else 0 := by
    ext a b
    simp only [Matrix.neg_apply, diagonal_apply]
    split_ifs <;> simp
  have h2 : (-A).submatrix Fin.castSucc Fin.castSucc = -A.submatrix Fin.castSucc Fin.castSucc := rfl
  rw [det_fromBlocks_swap, h, det_fromBlocks_single, det_updateRow_last, det_updateRow_last, h2, det_neg, det_neg]
  simp only [Fintype.card_fin]
  ring

end Det

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem B_e_e (F : FlagD H r) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = diagonal (fun a => if a = Fin.last r then -F.T else 0) a b := by
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp [F.zz]
  · rename_i b
    simp [B_eq_zero_comm.1 (F.zperp b), diagonal_apply, (Fin.castSucc_ne_last b).symm]
  · rename_i a
    simp [F.zperp a, diagonal_apply, Fin.castSucc_ne_last]
  · rename_i a b
    simp [F.iso a b, diagonal_apply, Fin.castSucc_ne_last]

theorem gram_eq_fromBlocks (F F' : FlagD H r) :
    Gram F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -F.T else 0) (Zhat F F') (Zhat F F')ᴴ
      (diagonal fun a => if a = Fin.last r then -F'.T else 0) := by
  ext (a | a) (b | b)
  · exact B_e_e F a b
  · rfl
  · exact (H.herm _ _).symm
  · exact B_e_e F' a b

theorem det_gram (F F' : FlagD H r) : (Gram F F').det = (-1) ^ (r + 1) * Gval F F' := by
  rw [gram_eq_fromBlocks, det_fromBlocks_last, ← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose]
  rfl

theorem gram_det_statement : LemmaG := fun _ _ _ _ _ _ _ _ F F' => det_gram F F'

theorem isTransv_iff_gval : ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), IsTransv F F' ↔ Gval F F' ≠ 0 := by
  intro K V _ _ _ _ _ H r F F'
  rw [isTransv_iff_gram, det_gram]
  simp

end GlobalTheory.SA.TransvG
