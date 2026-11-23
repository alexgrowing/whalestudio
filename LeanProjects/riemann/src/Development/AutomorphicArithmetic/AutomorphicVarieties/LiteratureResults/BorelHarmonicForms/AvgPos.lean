import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open MeasureTheory
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Bor.avgPos :
    UpperTheory.V.Lit.Bor.AvgPos := by
  intro K _ _ _ _ _ d ρ hρ
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  have hint : ∀ f : K → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : ∀ i j, Continuous fun h : K => ρ h⁻¹ i j := fun i j => (hρ i j).comp continuous_inv
  let F : K → Matrix (Fin d) (Fin d) ℂ := fun h => (ρ h⁻¹)ᴴ * ρ h⁻¹
  have hFc : ∀ a b, Continuous fun h => F h a b := by
    intro a b
    simp only [F, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact continuous_finset_sum _ fun l _ => (continuous_star.comp (hc l a)).mul (hc l b)
  have hlin : ∀ (A C : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d),
      (A * Matrix.of (fun a b => ∫ h, F h a b ∂μ) * C) i j = ∫ h, (A * F h * C) i j ∂μ := by
    intro A C i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_finset_sum]
      · congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_const_mul]
      · intro a _
        exact hint _ (continuous_const.mul (hFc a b))
    · intro b _
      exact hint _ ((continuous_finset_sum _ fun a _ => continuous_const.mul (hFc a b)).mul
        continuous_const)
  refine ⟨Matrix.of fun a b => ∫ h, F h a b ∂μ, ?_, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.of_apply]
      rw [show star (∫ h, F h j i ∂μ) = ∫ h, star (F h j i) ∂μ from integral_conj.symm]
      congr 1
      funext h
      exact (Matrix.isHermitian_conjTranspose_mul_self (ρ h⁻¹)).apply i j
    · intro x hx
      have hq : ∀ h, star x ⬝ᵥ (F h *ᵥ x) = star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        intro h
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      have hdot : star x ⬝ᵥ (Matrix.of (fun a b => ∫ h, F h a b ∂μ) *ᵥ x) =
          ∫ h, star x ⬝ᵥ (F h *ᵥ x) ∂μ := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_const_mul, integral_mul_const]
          · intro j _
            exact hint _ (continuous_const.mul ((hFc i j).mul continuous_const))
        · intro i _
          exact hint _ (continuous_finset_sum _ fun j _ =>
            continuous_const.mul ((hFc i j).mul continuous_const))
      have hre : ∀ h, star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) =
          ((star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re : ℂ) := by
        intro h
        have h0 := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).2
        rw [Complex.zero_im] at h0
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]
          exact h0.symm
      have hyc : ∀ l, Continuous fun h => (ρ h⁻¹ *ᵥ x) l := by
        intro l
        simp only [Matrix.mulVec, dotProduct]
        exact continuous_finset_sum _ fun j _ => (hc l j).mul continuous_const
      have hdc : Continuous fun h => star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        simp only [dotProduct, Pi.star_apply]
        exact continuous_finset_sum _ fun l _ => (continuous_star.comp (hyc l)).mul (hyc l)
      rw [hdot]
      simp only [hq]
      rw [congrArg (integral μ) (funext hre), integral_complex_ofReal, Complex.zero_lt_real]
      rw [integral_pos_iff_support_of_nonneg]
      · have hsupp : Function.support (fun h => (star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re) =
            Set.univ := by
          ext h
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          intro h0
          have hz : star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) = 0 := by
            rw [hre h, h0, Complex.ofReal_zero]
          rw [dotProduct_star_self_eq_zero] at hz
          apply hx
          have e : ρ h *ᵥ (ρ h⁻¹ *ᵥ x) = x := by
            rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
          rw [← e, hz, Matrix.mulVec_zero]
        rw [hsupp]
        exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
      · intro h
        have := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).1
        simpa using this
      · exact (Complex.continuous_re.comp hdc).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro k
    ext i j
    rw [hlin]
    have hF : ∀ h, (ρ k)ᴴ * F h * ρ k = F (k⁻¹ * h) := by
      intro h
      simp only [F, _root_.mul_inv_rev, inv_inv, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [hF]
    exact integral_mul_left_eq_self (fun h => F h i j) k⁻¹
