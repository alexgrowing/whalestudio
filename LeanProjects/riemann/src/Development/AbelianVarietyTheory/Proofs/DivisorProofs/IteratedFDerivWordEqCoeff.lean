import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem sum_words_eq_sum_multinomial {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [AddCommGroup D] [Module ℂ D] (k : ℕ) (G : (I →₀ ℕ) → D) :
    ∑ s : Fin k → I, G (∑ a, Finsupp.single (s a) 1) =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • G m := by
  let ℓ : MvPolynomial I ℂ →ₗ[ℂ] D := (MvPolynomial.basisMonomials I ℂ).constr ℂ G
  have hℓ : ∀ m, ℓ (MvPolynomial.monomial m 1) = G m := fun m => by
    have := (MvPolynomial.basisMonomials I ℂ).constr_basis ℂ G m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h1 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ s : Fin k → I, MvPolynomial.monomial (∑ a, Finsupp.single (s a) 1) 1 := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have h2 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • MvPolynomial.monomial m 1 := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    symm
    refine Finset.sum_nbij' (fun m => (m : I → ℕ)) (fun m => Finsupp.equivFunOnFinite.symm m)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simpa using hm
    · intro m hm
      simpa using hm
    · intro m _
      simp
    · intro m _
      simp
    · intro m _
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Nat.cast_smul_eq_nsmul,
        nsmul_eq_mul]
      simp
  have h := congrArg ℓ (h1.symm.trans h2)
  simpa only [map_sum, map_smul, hℓ] using h

theorem iteratedFDeriv_word_eq_coeff {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (s : Fin k → I) :
    iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) =
      ((∏ i, ((∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i).factorial : ℕ) : ℂ) *
        MvPowerSeries.coeff (∑ a, Finsupp.single (s a) 1) (GlobalTheory.taylor f) := by
  have hl : ((List.ofFn s : List I) : Multiset I) =
      Finsupp.toMultiset (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) := by
    rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map s _),
      Multiset.map_map]
    rfl
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, List.map_ofFn,
    GlobalTheory.lineDerivList_ofFn hf, mul_inv_cancel_left₀ (GlobalTheory.cast_prod_factorial_ne_zero _)]
  rfl

theorem taylor_eq_sum_coeff_taylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 →
    GlobalTheory.PeriodFamily.taylor N t f = ∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m (GlobalTheory.taylor f) • ∏ i, t i ^ m i := by
  intro I _ _ D _ _ N t f hf
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp : ∀ s : Fin k → I, ∏ a, t (s a) =
      ∏ i, t i ^ (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i := fun s => by
    simp only [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Finsupp.single_apply]
  simp only [iteratedFDeriv_word_eq_coeff hf, hp]
  rw [sum_words_eq_sum_multinomial k fun m : I →₀ ℕ =>
    ((k.factorial : ℂ)⁻¹ * (((∏ i, (m i).factorial : ℕ) : ℂ) *
      MvPowerSeries.coeff m (GlobalTheory.taylor f))) • ∏ i, t i ^ m i]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hk : ∑ i, m i = k := (Finset.mem_finsuppAntidiag.1 hm).1
  have hs : ((∏ i, (m i).factorial : ℕ) : ℂ) * (Nat.multinomial Finset.univ m : ℂ) =
      (k.factorial : ℂ) := by
    rw [← Nat.cast_mul, Nat.multinomial_spec, hk]
  have h0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_right_comm _ _ ((∏ i, (m i).factorial : ℕ) : ℂ),
    mul_comm (Nat.multinomial _ _ : ℂ), hs, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.PeriodFamily
