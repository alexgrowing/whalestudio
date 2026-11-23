import Mathlib
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory

theorem natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal :
    ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal →
      ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) →
      ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) →
        la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  intro l c K L _ _ _ _ _ la hl hD y hy
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d₀ ∈ differentIdeal (𝓞 K) (𝓞 L), d₀ ∉ la.asIdeal ^ (c + 1) := by
    by_contra h
    push_neg at h
    exact hD (Ideal.dvd_iff_le.mpr h)
  have h1 : la.intValuation ((l : 𝓞 L) ^ c) ≤ WithZero.exp (-(c : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ c).mpr (Ideal.pow_mem_pow hl c)
  have h2 : WithZero.exp (-(c : ℤ)) ≤ la.intValuation d₀ := by
    rw [HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le]
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem la,
      HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity, not_le] at hd₀
    rw [← ENat.lt_natCast_add_one_iff]
    exact_mod_cast hd₀
  have hyd := hy d₀ hd₀D
  have e1 : la.valuation L (d₀ : L) = la.intValuation d₀ := la.valuation_of_algebraMap (K := L) d₀
  have e2 : la.valuation L ((l : L) ^ c) = la.intValuation ((l : 𝓞 L) ^ c) := by
    rw [← la.valuation_of_algebraMap (K := L)]
    simp
  rw [Valuation.map_mul] at hyd ⊢
  calc la.valuation L ((l : L) ^ c) * la.valuation L y
      ≤ la.valuation L (d₀ : L) * la.valuation L y := by
        gcongr
        rw [e1, e2]
        exact h1.trans h2
    _ = la.valuation L y * la.valuation L (d₀ : L) := mul_comm _ _
    _ ≤ 1 := hyd

end GlobalTheory
