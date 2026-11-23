import Mathlib

namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

theorem isUpperTriangular_conjTranspose_iff {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  constructor
  · intro h i j hij
    have := h (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
    simpa [conjTranspose_apply] using this
  · intro h i j hij
    have := h (show OrderDual.toDual i < OrderDual.toDual j from hij)
    simp [conjTranspose_apply, this]

section Existence

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_isUpperTriangular_conjTranspose_mul_self {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ Rᴴ * R = S := by
  have hLi : (LDL.lowerInv hS).IsLowerTriangular := fun i j hij =>
    LDL.lowerInv_triangular hS (OrderDual.toDual_lt_toDual.1 hij)
  have hL : (LDL.lower hS).IsLowerTriangular := blockTriangular_inv_of_blockTriangular hLi
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible (LDL.lowerInv hS)))
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  set d : n → ℝ := fun i => RCLike.re (LDL.diagEntries hS i)
  have hd : ∀ i, LDL.diagEntries hS i = (d i : 𝕜) := fun i => by
    obtain ⟨_, him⟩ := RCLike.pos_iff.1 (hpos i)
    rw [← RCLike.re_add_im (LDL.diagEntries hS i), him]; simp [d]
  have hd0 : ∀ i, 0 ≤ d i := fun i => (RCLike.pos_iff.1 (hpos i)).1.le
  refine ⟨diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ,
    (blockTriangular_diagonal _).mul (isUpperTriangular_conjTranspose_iff.2 hL), ?_⟩
  have hsq : (diagonal (fun i => (Real.sqrt (d i) : 𝕜)))ᴴ * diagonal (fun i => (Real.sqrt (d i) : 𝕜))
      = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1; funext i
    rw [hd i, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hd0 i)]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc LDL.lower hS * (diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        (diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ)
      = LDL.lower hS * ((diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        diagonal (fun i => (Real.sqrt (d i) : 𝕜))) * (LDL.lower hS)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [hsq, LDL.lower_conj_diag]

end Existence

section Existence2

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem star_mul_self_norm_div {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by
  rw [star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm, RCLike.conj_mul, ← sq]
  exact div_self (pow_ne_zero 2 (by simpa using hx))

theorem exists_cholesky {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by
  obtain ⟨R, hR, hRS⟩ := exists_isUpperTriangular_conjTranspose_mul_self hS
  have hdet : S.det ≠ 0 := (isUnit_iff_isUnit_det S).1 hS.isUnit |>.ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    have : R.det ≠ 0 := by
      intro h; apply hdet; rw [← hRS, det_mul, h, mul_zero]
    rw [det_of_isUpperTriangular hR] at this
    exact fun i => Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)
  refine ⟨diagonal (fun i => (‖R i i‖ : 𝕜) / R i i) * R, fun i => ‖R i i‖,
    (blockTriangular_diagonal _).mul hR, fun i => norm_pos_iff.2 (hRi i), fun i => ?_, ?_⟩
  · rw [diagonal_mul, div_mul_cancel₀ _ (hRi i)]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _)ᴴ,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    have : (fun i => (star (fun i => (‖R i i‖ : 𝕜) / R i i)) i * ((‖R i i‖ : 𝕜) / R i i)) =
        fun _ => 1 := funext fun i => star_mul_self_norm_div (hRi i)
    rw [this, diagonal_one, Matrix.one_mul, hRS]
end Existence2

end CompanionTheory.D.gk.admitted.CholeskyDecomposition
