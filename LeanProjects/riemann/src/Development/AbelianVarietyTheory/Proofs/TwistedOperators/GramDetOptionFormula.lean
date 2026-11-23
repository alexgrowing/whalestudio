import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory

theorem gram_det_option_orth {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (w0 : A0 k) (y : ι → A0 k)
    (κ t : ι → ℝ) (h : ∀ i, ⟪y i, w0⟫_ℝ = 0) :
    (Matrix.gram ℝ (fun o : Option ι => o.elim w0 fun i => κ i • y i + t i • w0)).det =
      ‖w0‖ ^ 2 * (∏ i, κ i ^ 2) * (Matrix.gram ℝ y).det := by
  set e : Option ι ≃ ι ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit.{0} ι
  set A : Matrix (ι ⊕ PUnit.{1}) (ι ⊕ PUnit.{1}) ℝ :=
    Matrix.fromBlocks (Matrix.diagonal κ) (Matrix.of fun i _ => t i) 0 1 with hA
  set G : Matrix (ι ⊕ PUnit.{1}) (ι ⊕ PUnit.{1}) ℝ :=
    Matrix.fromBlocks (Matrix.gram ℝ y) 0 0 (Matrix.of fun _ _ => ‖w0‖ ^ 2) with hG
  have h' : ∀ i, ⟪w0, y i⟫_ℝ = 0 := fun i => by rw [real_inner_comm]; exact h i
  have key : Matrix.reindex e e
      (Matrix.gram ℝ (fun o : Option ι => o.elim w0 fun i => κ i • y i + t i • w0)) = A * G * A.transpose := by
    rw [hA, hG, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext (i | i) (j | j) <;>
    simp [e, Matrix.gram_apply, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, h, h', Matrix.mul_apply, Matrix.diagonal, real_inner_self_eq_norm_sq] <;>
    ring
  have hdA : A.det = ∏ i, κ i := by
    rw [hA, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Matrix.det_one, mul_one]
  have hdG : G.det = (Matrix.gram ℝ y).det * ‖w0‖ ^ 2 := by
    rw [hG, Matrix.det_fromBlocks_zero₂₁]
    congr 1
    rw [Matrix.det_unique]
    rfl
  rw [← Matrix.det_reindex_self e, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdA, hdG,
    Finset.prod_pow]
  ring

end GlobalTheory
