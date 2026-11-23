import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
