import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetMul

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section Lin

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} (l : ℕ) [Fact l.Prime]

theorem applyTerm_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyTerm l (T1 + T2) μ c = applyTerm l T1 μ c + applyTerm l T2 μ c := by
  simp [applyTerm, mul_add, map_add]

theorem applyAt0_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (T1 + T2) P = applyAt0 N0 N1 l T1 P + applyAt0 N0 N1 l T2 P := by
  simp only [applyAt0_eq_sum, applyTerm_addT, Finset.sum_add_distrib]

theorem applyAt0_zeroT (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (0 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) P = 0 := by
  simp [applyAt0_eq_sum, applyTerm]

theorem applyAt0_smulT (a : ℂ_[l]) (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (a • T) P = a • applyAt0 N0 N1 l T P := by
  simp only [applyAt0_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [applyTerm, MvPolynomial.smul_monomial, map_smul, smul_eq_mul]
  congr 1
  ring

theorem applyAt0_sumT {ι : Type*} (s : Finset ι) (T : ι → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (∑ i ∈ s, T i) P = ∑ i ∈ s, applyAt0 N0 N1 l (T i) P := by
  induction s using Finset.induction_on with
  | empty => simp [applyAt0_zeroT]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, applyAt0_addT, ih]

theorem degree_snd_le (μ : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ Finsupp.degree μ := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply]
  calc ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 j
      = ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, μ (Sum.inr j) := by
        simp [Finsupp.snd_sumFinsuppEquivProdFinsupp]
    _ = ∑ i ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support.map Function.Embedding.inr, μ i := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ i ∈ μ.support, μ i := by
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        simp only [Finset.mem_map, Finsupp.mem_support_iff, Finsupp.snd_sumFinsuppEquivProdFinsupp] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        simpa using hj

theorem applyAt0_eq_zero_of_order (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ)
    (h : (P.totalDegree : ℕ∞) < T.order) : applyAt0 N0 N1 l T P = 0 := by
  rw [applyAt0_eq_sum]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hd : Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ P.totalDegree :=
    (degree_snd_le μ).trans (by rw [Finsupp.degree_apply]; exact MvPolynomial.le_totalDegree hμ)
  have : MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_le_of_lt (by exact_mod_cast hd) h)
  unfold applyTerm
  rw [this, mul_zero, map_zero]

end Lin

section Trunc

variable {σ : Type*} [Finite σ] {K : Type*} [Field K]

theorem trunc_split (n : ℕ) (U : MvPowerSeries σ K) :
    ∃ (S : Finset (σ →₀ ℕ)) (V : MvPowerSeries σ K),
      U = (∑ k ∈ S, MvPowerSeries.monomial k (MvPowerSeries.coeff k U)) + V ∧ (n : ℕ∞) < V.order := by
  let Q := MvPowerSeries.truncTotal (n + 1) U
  refine ⟨Q.support, U - (Q : MvPowerSeries σ K), ?_, ?_⟩
  · have hQ : (Q : MvPowerSeries σ K) = ∑ k ∈ Q.support, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) := by
      conv_lhs => rw [Q.as_sum]
      rw [show ((∑ k ∈ Q.support, MvPolynomial.monomial k (MvPolynomial.coeff k Q) : MvPolynomial σ K) :
          MvPowerSeries σ K) = ∑ k ∈ Q.support, ((MvPolynomial.monomial k (MvPolynomial.coeff k Q) :
          MvPolynomial σ K) : MvPowerSeries σ K) from map_sum (MvPolynomial.coeToMvPowerSeries.ringHom) _ _]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [MvPolynomial.coe_monomial]
      congr 1
      rw [MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with h
      · rfl
      · exact absurd hk (by rw [MvPolynomial.mem_support_iff, MvPowerSeries.coeff_truncTotal_eq_ite, if_neg h]; simp)
    rw [← hQ]; ring
  · have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ (U - (Q : MvPowerSeries σ K)).order := by
      refine MvPowerSeries.le_order fun d hd => ?_
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite, if_pos, sub_self]
      exact_mod_cast hd
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) h1

end Trunc

end PI.OrbJet.OJ

end
