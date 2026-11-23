import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumInnerBasisSqEqAdjoint
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

open CompactHaarProbability in
theorem fF_conj_pmat_eq_op_inv_mul_fF_mul_op {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε) (z : PCoord ε → ℂ) :
    fF ε lam T (toMK k⁻¹ * pmat z * toMK k) = T.op k⁻¹ * fF ε lam T (pmat z) * T.op k := by
  rw [fF_eq_integral, fF_eq_integral]
  have h1 : ∀ (c : ℂ) (I : T.V →L[ℂ] T.V), T.op k⁻¹ * (c • I) * T.op k = c • conjE T k⁻¹ I := by
    intro c I
    rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc]
  rw [h1, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  conv_rhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have he : toMK (k * x)⁻¹ * pmat z * toMK (k * x) = toMK x⁻¹ * (toMK k⁻¹ * pmat z * toMK k) * toMK x := by
    rw [_root_.mul_inv_rev, hm, hm]
    simp only [Matrix.mul_assoc]
  have hop : T.op k⁻¹ * (T.op (k * x) * projW T * T.op (k * x)⁻¹) * T.op k = T.op x * projW T * T.op x⁻¹ := by
    rw [_root_.mul_inv_rev, op_mul, op_mul]
    simp only [mul_assoc]
    rw [op_inv_mul, mul_one, ← mul_assoc (T.op k⁻¹), op_inv_mul, one_mul]
  beta_reduce
  rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc, he, hop]

theorem sum_norm_adjoint_sq_eq_hsOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [CompleteSpace V] (A : V →L[ℂ] V) :
    ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 = hsOp A := by
  unfold hsOp
  set b := stdOrthonormalBasis ℂ V
  have h1 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 = ∑ j, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := by
    intro i
    rw [← b.sum_sq_norm_inner_right]
    refine sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have h2 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := fun j => (b.sum_sq_norm_inner_right _).symm
  simp_rw [h1, h2]
  exact sum_comm

theorem hsOp_ge_integral {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (A : T.V →L[ℂ] T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε) ≤ hsOp A := by
  set b := stdOrthonormalBasis ℂ T.V
  set B := ContinuousLinearMap.adjoint A
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hpt : ∀ k : KG ε, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ≤ ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 := by
    intro k
    have hn : ‖T.op k T.w‖ = 1 := by rw [KType_norm_op_apply, T.w_norm]
    have e : ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 = ‖A (T.op k T.w)‖ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right]
      refine sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [e]
    have := norm_inner_le_norm (𝕜 := ℂ) (T.op k T.w) (A (T.op k T.w))
    rw [hn, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI1 : Integrable (fun k : KG ε => ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
    integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk (A.continuous.comp hc))).norm.pow 2)
  have hI2 : ∀ i, Integrable (fun k : KG ε => ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2) (dk ε) := fun i =>
    integrable_dk_of_continuous ((continuous_const.inner hc).norm.pow 2)
  have hmono := integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt
  rw [integral_finsetSum _ fun i _ => hI2 i] at hmono
  have hd : (0 : ℝ) ≤ Module.finrank ℂ T.V := Nat.cast_nonneg _
  calc (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε)
      ≤ (Module.finrank ℂ T.V : ℝ) * ∑ i, ∫ k, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) :=
        mul_le_mul_of_nonneg_left hmono hd
    _ = ∑ i, ‖B (b i)‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [kschur_coef, T.w_norm, one_pow, one_mul]
    _ = hsOp A := sum_norm_adjoint_sq_eq_hsOp A

open CompactHaarProbability in
theorem continuous_fF (ε : Fin n → Bool) (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous fun z : PCoord ε → ℂ => fF ε lam T (pmat z) := by
  have hf : Continuous (fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) • (T.op p.2 * projW T * T.op p.2⁻¹)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_potential_conj_prod lam).neg)).smul
      ((cont_conj T _).comp continuous_snd)
  have h2 := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun z k => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹))
    hf isCompact_univ
  simp only [Measure.restrict_univ] at h2
  have he : (fun z : PCoord ε → ℂ => fF ε lam T (pmat z)) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) :=
    funext fun z => fF_eq_integral lam T _
  rw [he]
  exact (continuous_const : Continuous fun _ : PCoord ε → ℂ => ((Module.finrank ℂ T.V : ℝ) : ℂ)).smul h2

theorem inner_fF_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε)
    (z : PCoord ε → ℂ) :
    ⟪T.w, fF ε lam T (pmat (adK k⁻¹ z)) T.w⟫_ℂ = ⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ := by
  rw [← conj_pmat_eq_adK, fF_conj_pmat_eq_op_inv_mul_fF_mul_op, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem formal_degree_inequality {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) := by
  have hpos : 0 < (Module.finrank ℂ T.V : ℝ) := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have := T.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
    exact_mod_cast Module.finrank_pos
  have l6 := lemma6a hF hd
  set D : ℝ := (Module.finrank ℂ T.V : ℝ) with hD
  set G : (PCoord ε → ℂ) → ℝ := fun z => ‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 with hG
  set h : KG ε → (PCoord ε → ℂ) → ℝ :=
    fun k z => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2 * Jac z with hh
  have hFc := continuous_fF ε lam T
  have hJc := pb_jac_continuous ε
  have hGc : Continuous G := (continuous_const.inner (hFc.clm_apply continuous_const)).norm.pow 2
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hhc : Continuous (Function.uncurry h) := by
    have a : Continuous fun p : KG ε × (PCoord ε → ℂ) => T.op p.1 T.w := hc.comp continuous_fst
    exact ((a.inner ((hFc.comp continuous_snd).clm_apply a)).norm.pow 2).mul (hJc.comp continuous_snd)
  have s1 : ∀ k : KG ε, ∫⁻ z, ENNReal.ofReal (h k z) = ∫⁻ z, ENNReal.ofReal (G z * Jac z) := by
    intro k
    have hm : Measurable fun z => ENNReal.ofReal (G z * Jac z) :=
      ENNReal.measurable_ofReal.comp (hGc.mul hJc).measurable
    rw [← (adK_measurePreserving k⁻¹).lintegral_comp hm]
    refine lintegral_congr fun z => ?_
    simp only [h, G, inner_fF_conj, jac_adK]
  have s2 : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ z, ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) := by
    have e : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ k, (∫⁻ z, ENNReal.ofReal (h k z)) ∂(dk ε) := by
      simp only [s1, lintegral_const, measure_univ, mul_one]
    rw [e, lintegral_lintegral_swap (f := fun k z => ENNReal.ofReal (h k z)) (μ := dk ε) (ν := volume)
      (ENNReal.measurable_ofReal.comp hhc.measurable).aemeasurable]
  have s3 : ∀ z, ENNReal.ofReal D * ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) ≤
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro z
    have hi : Integrable (fun k => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
      integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk ((fF ε lam T (pmat z)).continuous.comp hc))).norm.pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
      (Filter.Eventually.of_forall fun k => mul_nonneg (by positivity) (jacobian_nonneg z)),
      integral_mul_const, ← ENNReal.ofReal_mul hpos.le, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsOp_ge_integral T _) (jacobian_nonneg z))
  have s4 : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (G z * Jac z) ≤
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    rw [s2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono s3
  have s5 : ENNReal.ofReal D * (ENNReal.ofReal (cPQ ε) * ∫⁻ z, ENNReal.ofReal (G z * Jac z)) ≤
      ENNReal.ofReal D * ENNReal.ofReal (D / d) := by
    rw [← ENNReal.ofReal_mul hpos.le, show D * (D / d) = D ^ 2 / d by ring, l6, mul_left_comm]
    exact mul_le_mul_right s4 _
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).1 s5

theorem lintegral_fF_coeff_sq_le_finrank_div_fdeg {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) :=
  formal_degree_inequality hF hd

end ReciprocityTheory.ChartRestriction.DS
