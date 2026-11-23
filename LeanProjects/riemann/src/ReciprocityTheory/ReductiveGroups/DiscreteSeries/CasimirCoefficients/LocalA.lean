import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcA_exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))

lemma exists_local_matrix_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h

lemma continuous_matrix_exp_alt :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous

end LogL

lemma lcA_exists_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)

lemma lcA_exists_klog (ε : Fin n → Bool) : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ ∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      k ∈ Kset ε → inK ε (ℓ k) ∧ NormedSpace.exp (ℓ k) = k := by
  obtain ⟨L, hL1, hL2, hL3⟩ := lcA_exists_log (n := n)
  refine ⟨L, hL1, ?_⟩
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hA : Tendsto (fun k => (L k)ᴴ) (𝓝 1) (𝓝 0) := by
    have h := hL1.star
    rw [star_zero] at h
    exact h
  have hB : Tendsto (fun k => -(L k)) (𝓝 1) (𝓝 0) := by
    have h := hL1.neg
    rw [neg_zero] at h
    exact h
  have hC : Tendsto (fun k => Jm ε * L k * Jm ε) (𝓝 1) (𝓝 0) := by
    have h := (hL1.const_mul (Jm ε)).mul_const (Jm ε)
    rw [mul_zero, zero_mul] at h
    exact h
  filter_upwards [hL2, hA.eventually hL3, hB.eventually hL3, hC.eventually hL3] with k h2 hA' hB' hC' hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkk : kᴴ * k = 1 := by
    have h := hk'.1
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  have e1 : NormedSpace.exp ((L k)ᴴ) = kᴴ := by rw [Matrix.exp_conjTranspose, h2]
  have e2 : NormedSpace.exp (-(L k)) = kᴴ := by
    rw [Matrix.exp_neg, h2]
    exact Matrix.inv_eq_left_inv hkk
  have hstar : (L k)ᴴ = -(L k) := by
    rw [← hA', e1, ← e2, hB']
  have e3 : NormedSpace.exp (Jm ε * L k * Jm ε) = NormedSpace.exp (L k) := by
    have h := Matrix.exp_conj (Jm ε) (L k) hJu
    rw [hJinv] at h
    rw [h, h2, mul_assoc, hk'.2, ← mul_assoc, hJJ, one_mul]
  have e4 : Jm ε * L k * Jm ε = L k := by
    rw [← hC', e3, h2]
  have hcomm : L k * Jm ε = Jm ε * L k := by
    calc L k * Jm ε = Jm ε * L k * Jm ε * Jm ε := by rw [e4]
      _ = Jm ε * L k := by rw [mul_assoc, hJJ, mul_one]
  refine ⟨⟨?_, hcomm⟩, h2⟩
  show (L k)ᴴ * Jm ε + Jm ε * L k = 0
  rw [hstar, neg_mul, ← hcomm]
  first
  | exact neg_add_cancel _
  | simp

open scoped Matrix.Norms.L2Operator in
lemma lcA_polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

end ReciprocityTheory.ChartRestriction.DS.S7
