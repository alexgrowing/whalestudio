import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem so_prod_norm (x : E) : ∏ σ : E →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun σ => rfl),
    ← norm_prod, ← h, eq_ratCast, Complex.norm_ratCast]

theorem so_norm_ge (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    1 ≤ |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
  classical
  set B := RingOfIntegers.basis E
  set b := NumberField.integralBasis E
  have hb : ∀ i, b i = (B i : E) := fun i => NumberField.integralBasis_apply E i
  choose N0 hN using fun i j => hw (B i * B j)
  set N : Matrix _ _ ℤ := Matrix.of N0 with hNdef
  have hTA : Algebra.traceMatrix ℚ b * Algebra.leftMulMatrix b w = (N.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.map_apply, hNdef, Matrix.of_apply, ← hN i j]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have e : w * (b i * b j) = b i * (w * b j) := by ring
    rw [show ((B i * B j : 𝓞 E) : E) = b i * b j by rw [hb, hb]; push_cast; ring, e]
    conv_rhs => rw [← b.sum_repr (w * b j)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet := congrArg Matrix.det hTA
  rw [Matrix.det_mul, ← Algebra.discr_def, ← Algebra.norm_eq_matrix_det, ← NumberField.coe_discr,
    ← Int.cast_det] at hdet
  have hne : N.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdet
    rcases mul_eq_zero.1 hdet with h1 | h1
    · exact NumberField.discr_ne_zero E (by exact_mod_cast h1)
    · exact hw0 ((Algebra.norm_eq_zero_iff).1 h1)
  have h1 : (1 : ℚ) ≤ |(N.det : ℚ)| := by exact_mod_cast Int.one_le_abs hne
  calc (1 : ℚ) ≤ |(N.det : ℚ)| := h1
    _ = |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
      rw [← hdet, abs_mul, mul_comm]

theorem so_sum_sq_ge [IsCMField E] (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    2 ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  have hcard : (Finset.univ : Finset (E →+* ℂ)).card = Module.finrank ℚ E := by
    rw [Finset.card_univ, NumberField.Embeddings.card]
  have hn2 : 2 ≤ Module.finrank ℚ E := by
    have h1 := NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hnR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast (by omega : 0 < Module.finrank ℚ E)
  have hwt : ∑ _σ ∈ (Finset.univ : Finset (E →+* ℂ)), (1 / (Module.finrank ℚ E : ℝ)) = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Module.finrank ℚ E : ℝ))
    (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity) hwt (fun _ _ => by positivity)
  rw [Real.finset_prod_rpow Finset.univ (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity),
    Finset.prod_pow, so_prod_norm, ← Finset.mul_sum] at amgm
  have hX : 0 ≤ |(Algebra.norm ℚ w : ℝ)| := abs_nonneg _
  have hY : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have key : (1 : ℝ) ≤ |(Algebra.norm ℚ w : ℝ)| * |(discr E : ℝ)| := by
    have h := so_norm_ge w hw0 hw
    exact_mod_cast h
  have hrd : PT.rd E ^ 2 = (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    unfold PT.rd
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (|(discr E : ℝ)|) 2, ← Real.rpow_mul hY,
      ← Real.rpow_mul hY, mul_comm]
  have hprodge : 1 ≤ (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
      (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.one_le_rpow _ (by positivity)
    nlinarith [key, mul_nonneg hX hY]
  have hS : (Module.finrank ℚ E : ℝ) * (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) ≤
      ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left amgm hnR.le
    rwa [← mul_assoc, mul_one_div_cancel hnR.ne', one_mul] at h
  calc (2 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast hn2
    _ ≤ (Module.finrank ℚ E : ℝ) * ((|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := le_mul_of_one_le_right hnR.le hprodge
    _ = PT.rd E ^ 2 * ((Module.finrank ℚ E : ℝ) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := by rw [hrd]; ring
    _ ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := mul_le_mul_of_nonneg_left hS (sq_nonneg _)

theorem so_emb_inj (v : (E →+* ℂ) → ℂ)
    (h : ∀ i, ∑ σ : E →+* ℂ, v σ * σ (RingOfIntegers.basis E i : E) = 0) : v = 0 := by
  classical
  have hM : (NumberField.basisMatrix E).mulVec v = 0 := by
    ext i
    rw [NumberField.basisMatrix_eq_embeddingsMatrixReindex]
    simp only [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply,
      NumberField.integralBasis_apply, Pi.zero_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm]
    rw [← h (NumberField.equivReindex E i)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [mul_comm]
    rfl
  have h2 := congrArg (fun u => (⅟(NumberField.basisMatrix E)).mulVec u) hM
  simp only [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
