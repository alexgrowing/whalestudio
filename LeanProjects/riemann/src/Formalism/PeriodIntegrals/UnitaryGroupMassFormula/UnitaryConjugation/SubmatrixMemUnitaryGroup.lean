import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.TransferStep

noncomputable section

namespace PI.UConjT

open Matrix

lemma star_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : star z = z :=
  Complex.conj_eq_iff_im.mpr h

lemma blk_castSucc_castSucc (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.castSucc b) = h a b := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

lemma blk_castSucc_last (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

lemma blk_last_castSucc (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
    PI.UMultOne.blk n h (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

lemma blk_last_last (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) :
    PI.UMultOne.blk n h (Fin.last n) (Fin.last n) = 1 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_last]

lemma eq_blk_of_last {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0)
    (hrow : ∀ j, k (Fin.last n) (Fin.castSucc j) = 0) (hll : k (Fin.last n) (Fin.last n) = 1) :
    PI.UMultOne.blk n (k.submatrix Fin.castSucc Fin.castSucc) = k := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_last_last, hll]
    | cast b => rw [blk_last_castSucc, hrow]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_castSucc_last, hcol]
    | cast b => rw [blk_castSucc_castSucc, submatrix_apply]

lemma submatrix_mem_unitaryGroup {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hk : k ∈ unitaryGroup (Fin (n + 1)) ℂ) (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0) :
    k.submatrix Fin.castSucc Fin.castSucc ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at hk ⊢
  ext a b
  have hab := congrFun (congrFun hk (Fin.castSucc a)) (Fin.castSucc b)
  rw [mul_apply, Fin.sum_univ_castSucc] at hab
  simp only [star_eq_conjTranspose, conjTranspose_apply, hcol, zero_mul, add_zero,
    one_apply, Fin.castSucc_inj] at hab
  simpa [mul_apply, conjTranspose_apply, one_apply] using hab

theorem blockStep : BlockStep := by
  intro hS n g hg
  obtain ⟨u, hu, d, hgu, hreal⟩ := hS n g hg
  have hu1 : u * uᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hu
  have hu2 : uᴴ * u = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hu
  have hgeq : g = u * diagonal d * uᴴ := by
    rw [← hgu, Matrix.mul_assoc, hu1, Matrix.mul_one]
  set k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (uᴴ)ᵀ * uᴴ with hkdef
  have hkH : kᴴ = u * uᵀ := by
    rw [hkdef, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    ext i j
    simp [conjTranspose_apply]
  have hkk : k * kᴴ = 1 := by
    rw [hkH, hkdef, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu2, Matrix.one_mul,
      ← transpose_mul, hu1, transpose_one]
  have hkU : k ∈ unitaryGroup (Fin (n + 1)) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hkk
  have hconj : k * g * kᴴ = gᵀ := by
    rw [hkH, hgeq, hkdef, transpose_mul, transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc uᴴ u, hu2, Matrix.one_mul, ← Matrix.mul_assoc uᴴ u, hu2,
      Matrix.one_mul]

  have hkent : ∀ i j, k i j = ∑ l, star (u i l) * star (u j l) := by
    intro i j; simp [hkdef, mul_apply, conjTranspose_apply]
  have hu1e : ∀ i j, ∑ l, u i l * star (u j l) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hu1 i) j
    simpa [mul_apply, conjTranspose_apply, one_apply] using this
  have hcol : ∀ i, k i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
    intro i
    rw [hkent]
    have : ∑ l, star (u i l) * star (u (Fin.last n) l) = star (∑ l, u i l * star (u (Fin.last n) l)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_mul', star_star, star_eq_self_of_im_eq_zero (hreal l)]
    rw [this, hu1e]
    split_ifs <;> simp
  have hrow : ∀ j, k (Fin.last n) j = if Fin.last n = j then 1 else 0 := by
    intro j
    rw [hkent, ← hu1e]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_eq_self_of_im_eq_zero (hreal l)]
  have hcol' : ∀ i : Fin n, k (Fin.castSucc i) (Fin.last n) = 0 := by
    intro i; rw [hcol]; simp [Fin.castSucc_ne_last]
  have hrow' : ∀ j : Fin n, k (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j; rw [hrow]; simp [(Fin.castSucc_ne_last j).symm]
  have hll : k (Fin.last n) (Fin.last n) = 1 := by rw [hcol]; simp
  refine ⟨k.submatrix Fin.castSucc Fin.castSucc, submatrix_mem_unitaryGroup k hkU hcol', ?_⟩
  rw [eq_blk_of_last k hcol' hrow' hll]
  exact hconj

end PI.UConjT
