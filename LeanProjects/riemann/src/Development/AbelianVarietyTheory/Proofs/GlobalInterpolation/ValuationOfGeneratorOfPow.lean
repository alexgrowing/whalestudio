import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_of_generator_of_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K) (h : 𝔭.asIdeal ^ n = Ideal.span {π}) :
    𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact 𝔭.ne_bot (pow_eq_zero_iff'.mp h).1
  rw [show (π : K) = algebraMap (𝓞 K) K π from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    𝔭.intValuation_if_neg hπ, ← h, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr 𝔭.ne_bot) 𝔭.associates_irreducible,
    Associates.count_self 𝔭.associates_irreducible, mul_one]

end GlobalTheory
