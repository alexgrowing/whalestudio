import Mathlib

namespace GlobalTheory.IntegralNormAtMostOne

theorem norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hcon
  have h1 : 1 < ‖y‖ := not_le.mp hcon
  have h0 : 0 < ‖y‖ := lt_trans one_pos h1
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, one_smul] at hpy
  have heq : y ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, p.coeff i • y ^ i :=
    eq_neg_of_add_eq_zero_right hpy
  have hlt : ∀ (s : Finset ℕ), (∀ i ∈ s, i < p.natDegree) →
      ‖∑ i ∈ s, p.coeff i • y ^ i‖ < ‖y‖ ^ p.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using pow_pos h0 _
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [zsmul_eq_mul, norm_mul, norm_pow]
        have hc : ‖((p.coeff a : ℤ) : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        calc ‖((p.coeff a : ℤ) : ℂ_[l])‖ * ‖y‖ ^ a ≤ 1 * ‖y‖ ^ a :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg h0.le _)
          _ = ‖y‖ ^ a := one_mul _
          _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ h1 (hs a (Finset.mem_insert_self _ _))
      · exact ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
  have := hlt (Finset.range p.natDegree) fun i hi => Finset.mem_range.mp hi
  rw [← norm_neg, ← heq, norm_pow] at this
  exact lt_irrefl _ this

end GlobalTheory.IntegralNormAtMostOne
