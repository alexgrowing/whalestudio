import Formalism.LatticeSlopes.Statement

open Module Submodule

noncomputable section

namespace Formalism.F

theorem gram_sum_smul_eq_transpose_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] (v : ι → E) (P : Matrix ι κ ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, P i j • v i) = P.transpose * Matrix.gram ℝ v * P := by
  ext j k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem det_gram_basis_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ L) (c : Basis κ ℤ L) :
    (Matrix.gram ℝ (fun i => (b i : E))).det = (Matrix.gram ℝ (fun k => (c k : E))).det := by
  let e : ι ≃ κ := b.indexEquiv c
  let c' : Basis ι ℤ L := c.reindex e.symm
  have hc' : (Matrix.gram ℝ (fun k => (c k : E))).det = (Matrix.gram ℝ (fun i => (c' i : E))).det := by
    have hs : Matrix.gram ℝ (fun i => (c' i : E)) = (Matrix.gram ℝ (fun k => (c k : E))).submatrix e e := by
      ext i j
      simp [c', Matrix.gram_apply]
    rw [hs, Matrix.det_submatrix_equiv_self]
  rw [hc']
  let M : Matrix ι ι ℤ := c'.toMatrix b
  have hb : (fun i => (b i : E)) = fun i => ∑ k, (M.map (Int.cast : ℤ → ℝ)) k i • (c' k : E) := by
    funext i
    conv_lhs => rw [← c'.sum_repr (b i)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Matrix.map_apply, Int.cast_smul_eq_zsmul]
    rfl
  rw [hb, gram_sum_smul_eq_transpose_mul (fun k => (c' k : E)) (M.map (Int.cast : ℤ → ℝ)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det ^ 2 = 1 := by
    have h2 : M.det * (b.toMatrix c').det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip c' b, Matrix.det_one]
    have h3 : IsUnit M.det :=
      ⟨⟨M.det, (b.toMatrix c').det, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    rw [← Int.cast_det]
    rcases Int.isUnit_iff.1 h3 with h | h <;> rw [h] <;> norm_num
  linear_combination (Matrix.gram ℝ (fun i => (c' i : E))).det * hdet

theorem covol_eq_gram : CovolEqGram := by
  intro E _ _ _ L hL ι _ _ b
  unfold covol
  rw [dif_pos hL]
  congr 1
  exact det_gram_basis_eq L (Module.finBasis ℤ L) b

end Formalism.F
