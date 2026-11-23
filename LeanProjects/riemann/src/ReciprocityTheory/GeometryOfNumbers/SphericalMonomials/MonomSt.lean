import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonomStA

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

instance isProbabilityMeasure_sphProb (N : ℕ) : IsProbabilityMeasure (sphProb N) := by
  unfold sphProb
  exact Measure.isProbabilityMeasure_map sphMonom_measurable_normalize.aemeasurable

theorem sphProb_compl_sphere (D : ℕ) : sphProb (D + 1) {z | sqN z = 1}ᶜ = 0 := by
  unfold sphProb
  rw [Measure.map_apply sphMonom_measurable_normalize
    ((isClosed_eq sphMonom_continuous_sqN continuous_const).measurableSet.compl)]
  apply measure_mono_null (t := {0})
  · intro z hz
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hz
    rw [Set.mem_singleton_iff]
    by_contra h0
    exact hz (sphMonom_sqN_normalize z h0)
  · unfold gaussC
    exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

theorem integral_mono_sphProb_of_ne {D : ℕ} {a b : Fin (D + 1) → ℕ} (hab : a ≠ b) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) = 0 := by
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, b i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphMonom_f_smul a b)
  beta_reduce at hk
  have hG := integral_mono_mul_exp_of_ne hab one_pos
  simp only [one_mul] at hG
  rw [hG, zero_mul] at hk
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a b)]
  rcases mul_eq_zero.mp hk.symm with h | h
  · rw [h, mul_zero]
  · exfalso
    norm_cast at h
    exact (div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos).ne' h

theorem integral_mono_sq_sphProb {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ∫ z, ‖monoC a z‖ ^ 2 ∂(sphProb (D + 1)) = monoNormSq a := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ z : Fin (D + 1) → ℂ,
      ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (monoC a z) * monoC a z := fun z => by
    rw [Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a a)]
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, a i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC a z) (sphMonom_f_smul a a)
  beta_reduce at hk
  have hG := integral_mono_sq_mul_exp a one_pos
  simp only [one_mul, one_pow, div_one] at hG
  have hG' : ∫ z, starRingEnd ℂ (monoC a z) * monoC a z * (Real.exp (-sqN z) : ℂ) =
      ((Real.pi ^ (D + 1) * ((∏ i, (a i).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← hG, ← integral_complex_ofReal]
    congr 1; funext z
    rw [Complex.ofReal_mul, e]
  rw [hG', sphMonom_gamma D 0 0 rfl, sphMonom_gamma D (∑ i, a i) _ rfl] at hk
  have hR : (((((D + ∑ i, a i).factorial : ℕ) : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    norm_cast; positivity
  simp only [Nat.add_zero] at hk
  rw [eq_div_of_mul_eq hR hk.symm]
  unfold monoNormSq
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (((D + ∑ i, a i).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [add_comm (∑ i, a i) D]
  push_cast
  field_simp

end ReciprocityTheory.GeometryOfNumbersTheory
