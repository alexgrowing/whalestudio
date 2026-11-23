import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace HadamardGramBound

theorem det_gram_le_prod_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have hK : Module.finrank ℝ K = Fintype.card (Fin n) := finrank_span_eq_card hw
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let w' : Fin n → K := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hg : Matrix.gram ℝ w = Matrix.gram ℝ w' := by
    ext i j
    simp [Matrix.gram_apply, w']
  let gb := InnerProductSpace.gramSchmidtOrthonormalBasis hK w'
  have hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'
  rw [hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]
  have hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w' := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => ?_)
  have h1 := abs_real_inner_le_norm (gb i) (w' i)
  rw [gb.orthonormal.1 i, one_mul] at h1
  have h2 : ‖w' i‖ = ‖w i‖ := rfl
  rw [← h2, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem gram_comb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → V) :
    Matrix.gram ℝ (fun i => ∑ j, M i j • b j) = M * Matrix.gram ℝ b * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem proof : HadamardGramBound.Statement := by
  intro V _ _ r v b hv hn hb
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb i)
  set N : Matrix (Fin r) (Fin r) ℝ := (Matrix.of M).map (Int.cast : ℤ → ℝ) with hNdef
  have hvN : v = fun i => ∑ j, N i j • b j := by
    funext i
    rw [← hM i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [N, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ v = N * Matrix.gram ℝ b * N.transpose := by
    rw [hvN]
    exact gram_comb N b
  have hdet : (Matrix.gram ℝ v).det = N.det ^ 2 * (Matrix.gram ℝ b).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hvpos : 0 < (Matrix.gram ℝ v).det := (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hbnn : 0 ≤ (Matrix.gram ℝ b).det := (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hNdet : N.det = (((Matrix.of M).det : ℤ) : ℝ) := by
    rw [hNdef]
    exact ((Int.castRingHom ℝ).map_det (Matrix.of M)).symm
  have hN0 : N.det ≠ 0 := by
    intro h
    rw [hdet, h] at hvpos
    simp at hvpos
  have hN1 : 1 ≤ N.det ^ 2 := by
    rw [hNdet] at hN0 ⊢
    have hd : (Matrix.of M).det ≠ 0 := by exact_mod_cast hN0
    have : (1 : ℤ) ≤ (Matrix.of M).det ^ 2 := by
      rcases lt_or_gt_of_ne hd with h | h <;> nlinarith
    exact_mod_cast this
  have hHad := det_gram_le_prod_norm_sq v hv
  have hprod : ∏ i, ‖v i‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun i _ => sq_nonneg _) fun i _ => pow_le_one₀ (norm_nonneg _) (hn i)
  change 0 < (Matrix.gram ℝ b).det ∧ (Matrix.gram ℝ b).det ≤ 1
  refine ⟨lt_of_le_of_ne hbnn fun h => ?_, ?_⟩
  · rw [hdet, ← h] at hvpos
    simp at hvpos
  · nlinarith

end HadamardGramBound

end GroundTheory.Heights₂.Heights
