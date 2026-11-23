import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LtOfBlkOfLt
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj Matrix

variable {K : Type*} [Field K] {N : ℕ} (p : Point K N)

abbrev cv (a : Fin N) : K := pval p.1 a.val

theorem cv_ne (a : Fin N) : cv p a ≠ 0 :=
  pval_ne p.1 (fun b hb => (p.2.1 b hb).1) a.val (by rw [p.2.2]; exact a.isLt)

theorem cv_pinv (a : Fin N) : cv p (pinv p a) = cv p a := pval_pinv p a

theorem pinv_inj {a b : Fin N} (h : pinv p a = pinv p b) : a = b := by
  have := congrArg (pinv p) h
  rwa [pinv_pinv, pinv_pinv] at this

theorem ptMat_mul_mono : ptMat p * mono (pinv p) (fun a => (cv p a)⁻¹) = 1 := by
  rw [ptMat_eq_mono]
  funext a b
  rw [mul_mono_apply _ (pinv_pinv p)]
  by_cases h : a = b
  · subst h
    simp only [mono, if_true, Matrix.one_apply_eq]
    rw [cv_pinv]; exact mul_inv_cancel₀ (cv_ne p a)
  · have hne : pinv p b ≠ pinv p a := fun e => h (pinv_inj p e).symm
    simp only [mono, hne, if_false, zero_mul, Matrix.one_apply_ne h]

theorem ptMat_inv : (ptMat p)⁻¹ = mono (pinv p) (fun a => (cv p a)⁻¹) :=
  Matrix.inv_eq_right_inv (ptMat_mul_mono p)

theorem conj_apply (M : Matrix (Fin N) (Fin N) K) (a b : Fin N) :
    ((ptMat p)⁻¹ * M * ptMat p) a b = (cv p a)⁻¹ * M (pinv p a) (pinv p b) * cv p b := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem conj'_apply (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (ptMat p * M * (ptMat p)⁻¹) i j = cv p i * M (pinv p i) (pinv p j) * (cv p j)⁻¹ := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem ptMat_isUnit : IsUnit (ptMat p).det := Matrix.isUnit_det_of_right_inverse (ptMat_mul_mono p)

def IsBlockDiagonalMatrix (X : Matrix (Fin N) (Fin N) K) : Prop := ∀ a b : Fin N, blkOf p.1 a.val ≠ blkOf p.1 b.val → X a b = 0

theorem blk_lt_of_lt {a b : Fin N} (hab : a < b) (hne : blkOf p.1 a.val ≠ blkOf p.1 b.val) :
    blkOf p.1 a.val < blkOf p.1 b.val :=
  lt_of_le_of_ne (blkOf_mono p.1 a.val b.val (le_of_lt hab)) hne

theorem X_of_st {β b : Matrix (Fin N) (Fin N) K} (hβ : IsLoUni β) (hb : IsUpUni b) (hW : β * ptMat p * b = ptMat p) :
    (ptMat p)⁻¹ * β * ptMat p = b⁻¹ ∧ UpU ((ptMat p)⁻¹ * β * ptMat p) ∧ IsBlockDiagonalMatrix p ((ptMat p)⁻¹ * β * ptMat p) := by
  have hu := ptMat_isUnit p
  have h1 : (ptMat p)⁻¹ * β * ptMat p * b = 1 := by
    rw [show (ptMat p)⁻¹ * β * ptMat p * b = (ptMat p)⁻¹ * (β * ptMat p * b) by simp only [Matrix.mul_assoc], hW,
      Matrix.nonsing_inv_mul _ hu]
  have hX : (ptMat p)⁻¹ * β * ptMat p = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  refine ⟨hX, ?_, ?_⟩
  · rw [hX]; exact upU_inv hb
  · intro a c hne
    rw [conj_apply]
    rcases lt_or_gt_of_ne (show a ≠ c from fun e => hne (by rw [e])) with h | h
    · have hb' := (lt_of_blk_lt p a c (blk_lt_of_lt p h hne)).2
      rw [(hβ _ _).1 hb', mul_zero, zero_mul]
    · have hup : UpU ((ptMat p)⁻¹ * β * ptMat p) := by rw [hX]; exact upU_inv hb
      have := (hup a c).1 h
      rwa [conj_apply] at this

theorem st_of_X {X : Matrix (Fin N) (Fin N) K} (hX : UpU X) (hB : IsBlockDiagonalMatrix p X) :
    IsLoUni (ptMat p * X * (ptMat p)⁻¹) ∧ IsUpUni X⁻¹ ∧
      ptMat p * X * (ptMat p)⁻¹ * ptMat p * X⁻¹ = ptMat p ∧ (ptMat p * X * (ptMat p)⁻¹).det = 1 := by
  have hu := ptMat_isUnit p
  have hXd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  refine ⟨fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, upU_inv hX, ?_, ?_⟩
  · rw [conj'_apply]
    by_cases hs : blkOf p.1 i.val = blkOf p.1 j.val
    · have := (pinv_lt_iff p i j hs).1 hij
      rw [(hX _ _).1 this, mul_zero, zero_mul]
    · have h2 := (lt_of_blk_lt p i j (blk_lt_of_lt p hij hs)).2
      have hs' : blkOf p.1 (pinv p i).val ≠ blkOf p.1 (pinv p j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact hs
      rw [hB _ _ hs', mul_zero, zero_mul]
  · subst hij
    rw [conj'_apply, (hX _ _).2 rfl, mul_one, mul_inv_cancel₀ (cv_ne p i)]
  · rw [Matrix.mul_assoc (ptMat p * X), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXd, Matrix.mul_one]
  · rw [Matrix.det_mul, Matrix.det_mul, upU_det hX, mul_one, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.det_one]

end Formalism.L2.SG.Pf.BlockPermutation
