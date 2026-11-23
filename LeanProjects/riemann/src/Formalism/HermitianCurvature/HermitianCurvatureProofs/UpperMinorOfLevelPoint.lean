import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMapApplyFirstBlock

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section zfull

variable {j : ℕ}

theorem zfull_apply (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (i l : Fin (j + 1)) :
    zfull Z τ i l = if h : i.val < j ∧ l.val < j then Z ⟨i.val, h.1⟩ ⟨l.val, h.2⟩
      else if i.val = j ∧ l.val = j then τ else 0 := by
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨l', rfl⟩ := finSumFinEquiv.surjective l
  unfold zfull U.blk2
  rcases i' with a | a <;> rcases l' with b | b <;>
    simp [Matrix.reindex_apply] <;> omega

theorem zfull_det (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end zfull

section point

variable {k r j : ℕ}

theorem x0_GV (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hM := (Formalism.FourierDecayAlt.P.slice_membership k (j + 1) (r - (j + 1))).1 _ γ hZf hγ
  exact Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM

theorem upper_minor_of_level_point (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.xi0 (x0 k r j hj Z τ γ) a' q =
      if hq : q.val < j + 1 then zfull Z τ ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0 := by
  unfold PBG.xi0
  rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  unfold x0
  rw [LeftFubiniLemmas.castM_apply']
  have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j + 1 - 1 - a'.val, by omega⟩) := by
    ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
  rw [hi, LeftFubiniLemmas.embedding_map_apply_last_block]
  by_cases hq : q.val < j + 1
  · rw [dif_pos (by simpa using hq), dif_pos hq]
    congr 1; ext; simp [Fin.val_rev]; omega
  · rw [dif_neg (by simpa using hq), dif_neg hq]

theorem lower_minor_of_level_point (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1)))
    (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < j + 1) :
    PBG.y0 (x0 k r j hj Z τ γ) a' q =
      if hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1 then
        star (zfull Z τ ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0 := by
  have hZf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  unfold PBG.y0
  rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
  have hgu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  unfold x0
  rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZf) hgu,
    LeftFubiniLemmas.castM_apply']
  have hjj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
    ext; rw [Ux3.block_index_first_val]; simp [eI]
  rw [hjj, LeftFubiniLemmas.embedding_map_apply_first_block]
  by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < j + 1
  · rw [dif_pos (by simp; omega), dif_pos hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
    congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
  · rw [dif_neg (by simp; omega), dif_neg hq]

end point

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
