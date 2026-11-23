import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

theorem eq_of_forall_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
      (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) → b ≤ WithZero.exp (-(n : ℤ))) → b ≤ a := by
    intro a b ha0 ha1 h
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log ha0, WithZero.exp_zero]
      exact ha1
    have hn : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
    have := h (-WithZero.log a).toNat (by rw [hn, neg_neg, WithZero.exp_log ha0])
    rwa [hn, neg_neg, WithZero.exp_log ha0] at this
  exact le_antisymm (key hb0 hb1 fun n => (h n).2) (key ha0 ha1 fun n => (h n).1)

section Conjugate

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

def smulPlace (σ : G) (w : HeightOneSpectrum B) : HeightOneSpectrum B where
  asIdeal := σ • w.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  ne_bot := by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact Ideal.map_bot

omit [IsDedekindDomain B] in
theorem smulPlace_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl

theorem intValuation_smulPlace (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, map_zero, map_zero]
  have hσr : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  refine eq_of_forall_le_exp_iff (intValuation_ne_zero _ _ hσr) (intValuation_ne_zero _ _ hr)
    (intValuation_le_one _ _) (intValuation_le_one _ _) fun n => ?_
  rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smulPlace_asIdeal, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul_iff

end Conjugate

section NumberField

variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]

theorem valuation_smulPlace (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have ha : σ (algebraMap (𝓞 M) M a) = algebraMap (𝓞 M) M (σ • a) := rfl
  have hb' : σ (algebraMap (𝓞 M) M b) = algebraMap (𝓞 M) M (σ • b) := rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smulPlace,
    intValuation_smulPlace]

theorem valuation_smulPlace_apply (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M x = w.valuation M (σ⁻¹ x) := by
  rw [← valuation_smulPlace σ w (σ⁻¹ x)]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ x).symm

end NumberField

section Unramified

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem valuation_algebraMap_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by
  rw [← valuation_liesOver L w W x,
    Ideal.ramificationIdx'_eq_ramificationIdx' w.asIdeal W.asIdeal
      (Ideal.map_ne_bot_of_ne_bot w.ne_bot),
    Ideal.ramificationIdx_eq_one, pow_one]

end Unramified

end GroundTheory.ProfCoh
