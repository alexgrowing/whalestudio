import Mathlib

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

def atPlace (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : Matrix (Fin a) (Fin a) ℂ :=
  M.map fun x => x w

def blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (blockDiagonal (atPlace M))

def unblk (e : Fin a × ι ≃ Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin a) (Fin a) (ι → ℂ) :=
  Matrix.of fun p q w => g (e (p, w)) (e (q, w))

def blkG (e : Fin a × ι ≃ Fin n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  blk e '' {M | IsUnit M}

theorem blk_apply (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin n) :
    blk e M i j = if (e.symm i).2 = (e.symm j).2 then M (e.symm i).1 (e.symm j).1 (e.symm i).2 else 0 := by
  rw [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    GlobalTheory.CompanionTheory.AdmGL.atPlace, Matrix.map_apply]

@[simp] theorem unblk_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    unblk e (blk e M) = M := by
  ext p q w
  simp [unblk, blk_apply]

theorem blk_injective (e : Fin a × ι ≃ Fin n) : Function.Injective (blk e) := by
  intro M N h
  rw [← GlobalTheory.CompanionTheory.AdmGL.unblk_blk e M, h, GlobalTheory.CompanionTheory.AdmGL.unblk_blk]

@[simp] theorem blk_one (e : Fin a × ι ≃ Fin n) : blk e 1 = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : e.symm i ≠ e.symm j := fun h'' => h (e.symm.injective h'')
    rw [Matrix.one_apply_ne h]
    by_cases h2 : (e.symm i).2 = (e.symm j).2
    · have h1 : (e.symm i).1 ≠ (e.symm j).1 := fun h1 => h' (Prod.ext h1 h2)
      rw [if_pos h2, Matrix.one_apply_ne h1, Pi.zero_apply]
    · rw [if_neg h2]

theorem atPlace_mul (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    atPlace (M * N) w = atPlace M w * atPlace N w := by
  ext p q
  simp [atPlace, Matrix.mul_apply, Finset.sum_apply]

@[simp] theorem blk_mul (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M * N) = blk e M * blk e N := by
  have h : GlobalTheory.CompanionTheory.AdmGL.atPlace (M * N) = fun w => GlobalTheory.CompanionTheory.AdmGL.atPlace M w * GlobalTheory.CompanionTheory.AdmGL.atPlace N w :=
    funext (GlobalTheory.CompanionTheory.AdmGL.atPlace_mul M N)
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply]
  rw [h, Matrix.blockDiagonal_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ e.symm _).symm

@[simp] theorem blk_add (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M + N) = blk e M + blk e N := by
  ext i j
  rw [Matrix.add_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply,
    GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_smul (e : Fin a × ι ≃ Fin n) (c : ℂ) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (c • M) = c • blk e M := by
  ext i j
  rw [Matrix.smul_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_conjTranspose (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e Mᴴ = (blk e M)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · rw [if_pos h, if_pos h.symm, Matrix.conjTranspose_apply, Pi.star_apply, h]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem continuous_blk (e : Fin a × ι ≃ Fin n) : Continuous (blk e) := by
  apply continuous_matrix
  intro i j
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · simp only [if_pos h]
    exact (continuous_apply _).comp (continuous_id.matrix_elem _ _)
  · simp only [if_neg h]
    exact continuous_const

theorem continuous_unblk (e : Fin a × ι ≃ Fin n) : Continuous (unblk e) := by
  apply continuous_matrix
  intro p q
  apply continuous_pi
  intro w
  simp only [GlobalTheory.CompanionTheory.AdmGL.unblk, Matrix.of_apply]
  exact continuous_id.matrix_elem _ _

theorem det_apply_place (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : M.det w = (atPlace M w).det :=
  RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) M

theorem det_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    (blk e M).det = ∏ w, (atPlace M w).det := by
  rw [blk, Matrix.det_reindex_self, Matrix.det_blockDiagonal]

theorem isUnit_blk_iff (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    IsUnit (blk e M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, GlobalTheory.CompanionTheory.AdmGL.det_blk, Pi.isUnit_iff]
  simp [isUnit_iff_ne_zero, GlobalTheory.CompanionTheory.AdmGL.det_apply_place, Finset.prod_ne_zero_iff]

theorem mem_blkG_iff (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ blkG e ↔ IsUnit g ∧ blk e (unblk e g) = g := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨(GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e M).2 hM, by rw [GlobalTheory.CompanionTheory.AdmGL.unblk_blk]⟩
  · rintro ⟨hg, hg'⟩
    refine ⟨GlobalTheory.CompanionTheory.AdmGL.unblk e g, ?_, hg'⟩
    rw [← hg'] at hg
    exact (GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e _).1 hg

end GlobalTheory.CompanionTheory.AdmGL

end
