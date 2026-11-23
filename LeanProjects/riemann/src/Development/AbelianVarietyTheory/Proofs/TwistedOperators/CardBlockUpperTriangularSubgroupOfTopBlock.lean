import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockPartitionOfEqTwoBlock

noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [Field κ] {r t : ℕ}

abbrev blkForm (g : GL (Fin (r + t)) κ) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) κ :=
  (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).submatrix finSumFinEquiv finSumFinEquiv

theorem blkForm_toBlocks₂₁ {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₁ = 0 := by
  ext i j
  simp only [toBlocks₂₁, blkForm, submatrix_apply, of_apply, Matrix.zero_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  apply hg
  have hj : (Fin.castAdd t j).val < r := j.2
  have hi : ¬ (Fin.natAdd r i).val < r := by simp
  simp only [blk2, hj, hi, if_true, if_false]
  exact Nat.zero_lt_one

theorem blkForm_eq {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    blkForm g = fromBlocks (blkForm g).toBlocks₁₁ (blkForm g).toBlocks₁₂ 0 (blkForm g).toBlocks₂₂ := by
  rw [← blkForm_toBlocks₂₁ hg, fromBlocks_toBlocks]

theorem det_blkForm_toBlocks22_ne_zero_of_mem_blockTri {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₂.det ≠ 0 := by
  have h1 : (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h2 : (blkForm g).det = (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det := det_submatrix_equiv_self _ _
  rw [blkForm_eq hg, det_fromBlocks_zero₂₁] at h2
  intro h; rw [h, mul_zero] at h2; exact h1 h2.symm

def blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) : GL (Fin (r + t)) κ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) (by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (A.isUnit.map Matrix.detMonoidHom).ne_zero (D.isUnit.map Matrix.detMonoidHom).ne_zero)

theorem blkForm_blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkForm (blkMk A D B) = fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ) := by
  ext i j
  simp [blkForm, blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem blkMk_mem (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkMk A D B ∈ blockTri (blk2 r) := by
  intro i j hij
  have key : r ≤ i.val ∧ j.val < r := by unfold blk2 at hij; split_ifs at hij <;> omega
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, by ext; simp; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = Fin.castAdd t j' := ⟨⟨j.val, key.2⟩, by ext; simp⟩
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem topBlock_upperTriangularBlockGL (hr : r ≤ r + t) (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    upperLeftBlock hr (blkMk A D B) = A := by
  ext i j
  rw [upper_block_val_submatrix hr (blkMk_mem A D B)]
  have : Fin.castLE hr = Fin.castAdd t := rfl
  rw [this]
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem upperLeftBlock_eq_blkForm_toBlocks11 (hr : r ≤ r + t) {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = (blkForm g).toBlocks₁₁ := by
  rw [upper_block_val_submatrix hr hg]
  ext i j
  rfl

def parSubEquiv (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) :
    parSub hr H ≃ H × GL (Fin t) κ × Matrix (Fin r) (Fin t) κ where
  toFun g := (⟨upperLeftBlock hr g, g.2.2⟩,
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1), (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂)
  invFun x := ⟨blkMk x.1 x.2.1 x.2.2, blkMk_mem _ _ _, by rw [topBlock_upperTriangularBlockGL]; exact x.1.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    have h1 := blkForm_blkMk (r := r) (t := t) (κ := κ) (upperLeftBlock hr g)
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1)) (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂
    have h2 := blkForm_eq g.2.1
    rw [upperLeftBlock_eq_blkForm_toBlocks11 hr g.2.1] at h1
    have h3 : blkForm (blkMk (upperLeftBlock hr g) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1))
        (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂) = blkForm (g : GL (Fin (r + t)) κ) := by
      exact h1.trans h2.symm
    ext i j
    have := congrFun (congrFun h3 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    simpa [blkForm] using this
  right_inv x := by
    obtain ⟨A, D, B⟩ := x
    refine Prod.ext (Subtype.ext (topBlock_upperTriangularBlockGL hr _ _ _)) (Prod.ext ?_ ?_)
    · apply Units.ext
      show (blkForm (blkMk A.1 D B)).toBlocks₂₂ = _
      rw [blkForm_blkMk]; rfl
    · show (blkForm (blkMk A.1 D B)).toBlocks₁₂ = _
      rw [blkForm_blkMk]; rfl

theorem card_parSub_eq (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) [Finite κ] :
    Nat.card (parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  rw [Nat.card_congr (parSubEquiv hr H), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin t → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin t),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_parSub : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ) (hr : r ≤ n), n = r + t →
    ∀ H : Subgroup (GL (Fin r) κ),
      Nat.card (GlobalTheory.ParIndex.parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  intro κ _ _ n r t hr hn H
  subst hn
  exact card_parSub_eq hr H

end GlobalTheory.ParIndex

end
