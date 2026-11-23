import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace GramContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem det_gram_le_prod {α : Type*} [Fintype α] [DecidableEq α] (y : α → V) :
    (Matrix.gram ℝ y).det ≤ ∏ a, ‖y a‖ ^ 2 := by
  by_cases hy : LinearIndependent ℝ y
  · let e := Fintype.equivFin α
    have h := HadamardGramBound.det_gram_le_prod_norm_sq (y ∘ e.symm) (hy.comp _ e.symm.injective)
    have hg : Matrix.gram ℝ (y ∘ e.symm) = (Matrix.gram ℝ y).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.gram_apply]
    rw [hg, Matrix.det_submatrix_equiv_self] at h
    rwa [Fintype.prod_equiv e.symm (fun i => ‖(y ∘ e.symm) i‖ ^ 2) (fun a => ‖y a‖ ^ 2) (fun _ => rfl)] at h
  · have h0 : (Matrix.gram ℝ y).det = 0 := by
      by_contra h; exact hy (Matrix.det_gram_ne_zero_iff_linearIndependent.mp h)
    rw [h0]; exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem gram_comb {α : Type*} [Fintype α] (M : Matrix α α ℝ) (y : α → V) :
    Matrix.gram ℝ (fun a => ∑ b, M a b • y b) = M * Matrix.gram ℝ y * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GramContraction

theorem GramContraction.proof : GramContraction.Statement := by
  intro ι κ _ _ _ _ V _ _ Ψ u w hΨ
  let e := EuclideanSpace.basisFun ι ℝ
  let U : Matrix ι ι ℝ := Matrix.of fun i j => u i j
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks U 0 0 1
  let y : ι ⊕ κ → V := Sum.elim (fun i => Ψ (e i)) w
  have hu : ∀ i, Ψ (u i) = ∑ j, U i j • Ψ (e j) := fun i => by
    conv_lhs => rw [← e.sum_repr (u i)]
    simp [U, e, map_sum, map_smul]
  have hfam : Sum.elim (Ψ ∘ u) w = fun a => ∑ b, M a b • y b := by
    funext a
    rcases a with i | k
    · simp [Fintype.sum_sum_type, M, y, hu]
    · simp [Fintype.sum_sum_type, M, y, Matrix.one_apply]
  have hGu : Matrix.gram ℝ u = U * U.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp [Matrix.gram_apply, U, PiLp.inner_apply, mul_comm]
  have hdet : (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det = U.det ^ 2 * (Matrix.gram ℝ y).det := by
    rw [hfam, GramContraction.gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one]
    ring
  have hP : ∏ i, ‖Ψ (e i)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun _ _ => sq_nonneg _) fun i _ => by
      have := hΨ (e i); rw [e.orthonormal.1 i] at this
      nlinarith [norm_nonneg (Ψ (e i))]
  have hW : 0 ≤ ∏ j, ‖w j‖ ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hH := GramContraction.det_gram_le_prod y
  rw [Fintype.prod_sum_type] at hH
  rw [hdet, hGu, Matrix.det_mul, Matrix.det_transpose, ← sq]
  refine mul_le_mul_of_nonneg_left (hH.trans ?_) (sq_nonneg _)
  simpa [y] using mul_le_of_le_one_left hW hP

end GroundTheory.Heights₂.Heights.HilbertSamuel
