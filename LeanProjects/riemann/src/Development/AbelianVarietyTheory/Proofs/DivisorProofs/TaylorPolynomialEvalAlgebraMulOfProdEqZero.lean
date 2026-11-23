import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff

open Filter Topology

namespace GlobalTheory.PeriodFamily

section

variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]

theorem exists_prod_dvd_monomial (t : I → D) (k : ℕ) :
    ∀ m : I →₀ ℕ, k ≤ m.degree → ∃ s : Fin k → I, ∏ a, t (s a) ∣ ∏ i, t i ^ m i := by
  induction k with
  | zero => intro m _; exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro m hm
    have h : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    obtain ⟨s, hs⟩ := ih m' (by rw [map_add, Finsupp.degree_single] at hm; omega)
    refine ⟨Fin.cons i s, ?_⟩
    have h1 : ∏ j, t j ^ (Finsupp.single i 1 : I →₀ ℕ) j = t i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finsupp.add_apply, pow_add,
      Finset.prod_mul_distrib, h1]
    exact mul_dvd_mul_left _ hs

variable [Algebra ℂ D]

theorem aeval_eq_zero_of_coeff_eq_zero {N : ℕ} {t : I → D}
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (P : MvPolynomial I ℂ)
    (hP : ∀ m : I →₀ ℕ, m.degree < N + 1 → P.coeff m = 0) : MvPolynomial.aeval t P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have h : N + 1 ≤ m.degree := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hm (hP m (by omega))
  obtain ⟨s, hs⟩ := exists_prod_dvd_monomial t (N + 1) m h
  rw [ht, zero_dvd_iff] at hs
  rw [hs, mul_zero]

omit [Algebra ℂ D] [CommRing D] in

theorem coeff_sum_monomial_finsuppAntidiag (N : ℕ) (F : MvPowerSeries I ℂ) (n : I →₀ ℕ)
    (hn : n.degree < N + 1) :
    MvPolynomial.coeff n (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) = MvPowerSeries.coeff n F := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← Finsupp.degree_eq_sum, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hn)]

theorem aeval_sum_monomial_finsuppAntidiag (N : ℕ) (t : I → D) (F : MvPowerSeries I ℂ) :
    MvPolynomial.aeval t (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  simp only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (t i))]

end

theorem taylor_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) =
        GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  intro I _ _ D _ _ N t ht f g hf hg
  change GlobalTheory.PeriodFamily.taylor N t (f * g) = _
  rw [GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ (hf.mul hg), GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hf, GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hg,
    GlobalTheory.taylor_mul hf hg, ← aeval_sum_monomial_finsuppAntidiag,
    ← aeval_sum_monomial_finsuppAntidiag, ← aeval_sum_monomial_finsuppAntidiag, ← map_mul,
    ← sub_eq_zero, ← map_sub]
  refine aeval_eq_zero_of_coeff_eq_zero ht _ fun m hm => ?_
  rw [MvPolynomial.coeff_sub, coeff_sum_monomial_finsuppAntidiag _ _ _ hm, MvPolynomial.coeff_mul,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, map_add] at hm
  rw [coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega),
    coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega)]

end GlobalTheory.PeriodFamily
