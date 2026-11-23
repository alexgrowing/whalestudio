import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastMCastM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def NFHypL : Prop :=
  ∀ (k r : ℕ) (a : C.LPt) (hle : D.ptSize a ≤ r) (g' : B.Mat k (r - D.ptSize a)), g' ∈ B.GV k (r - D.ptSize a) →
    D.IsLocPt a (D.ptSize a) →
    levelZeroPointOver a hle g' ∈ B.GV k r ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.xi0 (levelZeroPointOver a hle g') a' q =
        if hq : q.val < D.ptSize a then U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0) ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.y0 (levelZeroPointOver a hle g') a' q =
        if hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a then
          star (U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0)

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (i j : Fin (2 * b + k + 1)) :
    D.castM h g i j = g (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := rfl

theorem embedding_map_apply_last_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (c : Fin p)
    (j : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ (U.eB k p ρ (Sum.inr c)) j =
      if hj : j.val < p then Z c.rev ⟨j.val, hj⟩ else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dif_pos (by rw [Ux3.block_index_first_val]; exact y.isLt)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [Ux3.wMat_mul_apply]
    exact congrArg (Z c.rev) (Fin.ext (Ux3.block_index_first_val (k := k) (ρ := ρ) y).symm)
  · rw [dif_neg (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr]
  · rw [dif_neg (by rw [Ux3.block_index_last_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₂]

theorem embedding_map_apply_first_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (b : Fin p)
    (i : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ i (U.eB k p ρ (Sum.inl (Sum.inl b))) =
      if hi : p + (2 * ρ + k + 1) ≤ i.val then
        (G.wMat p * Z) ⟨i.val - (p + (2 * ρ + k + 1)), by omega⟩ b else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective i
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dif_neg (by rw [Ux3.block_index_first_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dif_neg (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dif_pos (by rw [Ux3.block_index_last_val]; omega)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    exact congrArg (fun c => (G.wMat p * Z) c b) (Fin.ext (by
      show (U.eB k p ρ (Sum.inr y)).val - (p + (2 * ρ + k + 1)) = y.val
      rw [Ux3.block_index_last_val]; omega)).symm

theorem normal_form_left_hypothesis : NFHypL := by
  intro k r a hle g' hg' hloc
  have hd : ∀ i, D.ptDiag a i ≠ 0 := fun i => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hloc.1 i i.2
  have hZ : (U.hMat (D.ptPerm a) (D.ptDiag a)).det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd
  have hM : U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g' ∈
      B.GV k (D.ptSize a + (r - D.ptSize a)) :=
    (Formalism.FourierDecayAlt.P.slice_membership k (D.ptSize a) (r - D.ptSize a)).1 _ g' hZ hg'
  refine ⟨Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM, fun a' q ha' => ?_, fun a' q ha' => ?_⟩
  · unfold PBG.xi0
    rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    unfold levelZeroPointOver
    rw [castM_apply']
    have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inr ⟨D.ptSize a - 1 - a'.val, by omega⟩) := by
      ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
    rw [hi, embedding_map_apply_last_block]
    by_cases hq : q.val < D.ptSize a
    · rw [dif_pos (by simpa using hq), dif_pos hq]
      congr 1; ext; simp [Fin.val_rev]; omega
    · rw [dif_neg (by simpa using hq), dif_neg hq]
  · unfold PBG.y0
    rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    have hgu : IsUnit g'.det := WeylGroupFacts.isUnit_of_uh hg'
    unfold levelZeroPointOver
    rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZ) hgu, castM_apply']
    have hj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
      ext; rw [Ux3.block_index_first_val]; simp [eI]
    rw [hj, embedding_map_apply_first_block]
    by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a
    · rw [dif_pos (by simp; omega), dif_pos hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
      congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
    · rw [dif_neg (by simp; omega), dif_neg hq]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
