import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.DenseCompl

theorem exists_eq_algebraMap_of_valued_le_one {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] {π : W}
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W)
    {a : v.adicCompletion Qq} (ha : Valued.v a ≤ 1) :
    ∃ L : W, a = algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) := by
  choose r hr using fun n : ℕ => GlobalTheory.Idele.exists_valued_sub_le v ha n
  have hle : ∀ m n : ℕ, m ≤ n → exp (-(n : ℤ)) ≤ exp (-(m : ℤ)) := fun m n h => by
    rw [exp_le_exp]; omega
  have hdiv : ∀ m n : ℕ, m ≤ n → π ^ m ∣ r n - r m := by
    intro m n hmn
    have h1 : v.valuation Qq (algebraMap W Qq (r n - r m)) ≤ exp (-(m : ℤ)) := by
      rw [← GlobalTheory.Idele.valued_algebraMap, map_sub, map_sub]
      have he : algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n)) -
          algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m)) =
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m))) -
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) := by ring
      rw [he]
      exact (Valuation.map_sub _ _ _).trans (max_le (hr m) ((hr n).trans (hle m n hmn)))
    obtain ⟨w, hw⟩ := (exists_eq_pow_mul_iff hπ v _ m).2 h1
    exact ⟨w, IsFractionRing.injective W Qq hw⟩
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := r) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hdiv m n hmn))
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero, ← Valuation.zero_iff Valued.v]
  refine eq_zero_of_forall_le_exp fun n => ?_
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  have h3 : Valued.v (algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L))) ≤
      exp (-(n : ℤ)) := by
    rw [GlobalTheory.Idele.valued_algebraMap]
    exact (exists_eq_pow_mul_iff hπ v _ n).1 ⟨w, by rw [hw]⟩
  have he : a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) =
      (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) +
      algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L)) := by
    rw [map_sub, map_sub]; ring
  rw [he]
  exact (Valuation.map_add _ _ _).trans (max_le (hr n) h3)

theorem surjective_algebraMap_adicCompletion : ∀ {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W)
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W),
    Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  intro W Qq _ _ _ _ _ _ π hπ hc v a
  by_cases ha : Valued.v a ≤ 1
  · obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v ha
    exact ⟨_, hL.symm⟩
  have ha0 : Valued.v a ≠ 0 := fun h => ha (h ▸ zero_le')
  set p := algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq π) with hpdef
  have hp : Valued.v p = exp (-1) := by
    rw [hpdef, GlobalTheory.Idele.valued_algebraMap, valuation_uniformiser hπ v]
  have hp0 : p ≠ 0 := fun h => exp_ne_zero (by rw [← hp, h, map_zero] : exp (-1 : ℤ) = 0)
  set m := (log (Valued.v a)).toNat
  have hva : Valued.v a = exp (log (Valued.v a)) := (exp_log ha0).symm
  have hle : Valued.v (a * p ^ m) ≤ 1 := by
    rw [map_mul, map_pow, hva, hp, ← exp_nsmul, ← exp_add, ← exp_zero, exp_le_exp]
    have := Int.self_le_toNat (log (Valued.v a))
    simp only [smul_neg, nsmul_eq_mul, mul_one]
    omega
  obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v hle
  refine ⟨algebraMap W Qq L / algebraMap W Qq π ^ m, ?_⟩
  rw [map_div₀, map_pow, ← hL, ← hpdef, mul_div_cancel_right₀ _ (pow_ne_zero _ hp0)]

end GlobalTheory.DenseCompl
