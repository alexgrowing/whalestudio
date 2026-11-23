import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff

open Filter Topology

namespace GlobalTheory.PeriodFamily

section Alg

variable {I R D : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing D] [Algebra R D]

omit [DecidableEq I] in

theorem mvAeval_add_of_mul_eq_zero (t n : I → D) (hn : ∀ i j, n i * n j = 0)
    (P : MvPolynomial I R) :
    MvPolynomial.aeval (fun i ↦ t i + n i) P =
      MvPolynomial.aeval t P + ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * n i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p j hp =>
    have h1 : (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * n j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hn, mul_zero]
    have h2 : ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
        (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * t j +
          MvPolynomial.aeval t p * n j := by
      have h3 : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
          MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i * t j +
            if j = i then MvPolynomial.aeval t p * n i else 0 := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.aeval_X,
          MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
    rw [map_mul, map_mul, hp, h2, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    linear_combination h1

theorem aeval_truncTotal_succ (N : ℕ) (t : I → D) (F : MvPowerSeries I R) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) F) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  have h : MvPowerSeries.truncTotal (N + 1) F =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F) := by
    ext d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finset.sum_ite_eq,
      Finset.mem_range, Finsupp.degree_eq_sum]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]

omit [Fintype I] [DecidableEq I] in

theorem ideal_pow_eq_bot_of_prod {J : Ideal D} {k : ℕ}
    (h : ∀ s : Fin k → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) : J ^ k = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  rw [List.prod_ofFn]
  exact h _ fun a => (f a).2

omit [DecidableEq I] in

theorem aeval_pderiv_truncTotal_mul {J : Ideal D} {N : ℕ} (hJ : J ^ (N + 1) = ⊥) {t : I → D}
    (ht : ∀ i, t i ∈ J) {x : D} (hx : x ∈ J) (F : MvPowerSeries I R) (i : I) :
    MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPowerSeries.truncTotal (N + 1) F)) * x =
      MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) (MvPowerSeries.pderiv R i F)) * x := by
  classical
  rw [← sub_eq_zero, ← sub_mul, ← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : N ≤ m.degree := by
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hm ?_
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_truncTotal _
      (by rw [map_add, Finsupp.degree_single]; omega), MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_pderiv, sub_self]
  have h1 : ∏ j, t j ^ m j ∈ J ^ N := by
    refine Ideal.pow_le_pow_right hdeg ?_
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (ht j) _
  have h2 : (∏ j, t j ^ m j) * x = 0 := by
    rw [← Ideal.mem_bot, ← hJ, pow_succ]
    exact Ideal.mul_mem_mul h1 hx
  rw [mul_assoc, h2, mul_zero]

end Alg

theorem taylor_add_of_mul_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  intro I _ _ D _ _ N t n hs hn f hf
  have key : ∀ (u : I → D) (g : (I → ℂ) → ℂ), AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N u g =
      MvPolynomial.aeval u (MvPowerSeries.truncTotal (N + 1) (GlobalTheory.taylor g)) := fun u g hg => by
    rw [aeval_truncTotal_succ, taylor_eq_sum_coeff_taylor N u g hg]
  rw [key _ _ hf, key _ _ hf, mvAeval_add_of_mul_eq_zero t n hn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key _ _ (GlobalTheory.analyticAt_fderiv_apply hf _), GlobalTheory.taylor_fderiv hf]
  exact aeval_pderiv_truncTotal_mul (ideal_pow_eq_bot_of_prod hs)
    (fun j => Ideal.subset_span (Or.inl ⟨j, rfl⟩)) (Ideal.subset_span (Or.inr ⟨i, rfl⟩)) _ i

end GlobalTheory.PeriodFamily
