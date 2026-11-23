import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ResidueUnit
import Mathlib

open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

private theorem count_coe_map_conj (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) :
    FractionalIdeal.count K v
        ((J.map (ringOfIntegersComplexConj K).toRingEquiv : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (J : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  set c := (ringOfIntegersComplexConj K).toRingEquiv with hc
  rcases eq_or_ne J 0 with rfl | hJ
  · simp [FractionalIdeal.count_zero]
  have hJ' : J.map c ≠ 0 := by
    intro h
    exact hJ ((Ideal.map_eq_bot_iff_of_injective c.injective).mp h)
  rw [FractionalIdeal.count_coe K v hJ', FractionalIdeal.count_coe K _ hJ]
  congr 1
  refine eq_of_forall_le_iff fun n => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ') v.associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (conjPrime v).associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  have h1 : (conjPrime v).asIdeal = v.asIdeal.comap c := rfl
  rw [h1, ← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

private theorem count_spanSingleton_conj_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K (a : K))) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := by
  have h := count_coe_map_conj v (Ideal.span {a})
  rw [Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton] at h
  exact h

theorem count_spanSingleton_conj (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K x)) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [FractionalIdeal.count_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := fun h => hx (by simp [h])
  have hb0 : algebraMap (𝓞 K) K b ≠ 0 := fun h => hx (by simp [h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (y z : K), y ≠ 0 → z ≠ 0 →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (y / z)) =
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) -
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ z) := by
    intro w y z hy hz
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hz)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, sub_eq_add_neg]
  rw [map_div₀, key _ _ _ (by simpa using ha0) (by simpa using hb0), key _ _ _ ha0 hb0]
  congr 1
  · exact count_spanSingleton_conj_int v a
  · exact count_spanSingleton_conj_int v b

theorem count_fromBase (v : HeightOneSpectrum (𝓞 K)) {b : IdealGroup K} (hb : b ∈ fromBase K) :
    FractionalIdeal.count K v (b : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (b : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨I, hI⟩ := hb
  obtain ⟨d, J, hd, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))
  have hbI : (b : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.extendedHom K (𝓞 K)
      (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K)) := by
    rw [← hI]; rfl
  have hd1 : (FractionalIdeal.spanSingleton (𝓞 (maximalRealSubfield K))⁰
      (algebraMap _ (maximalRealSubfield K) d)⁻¹) =
      ((Ideal.span {d} : Ideal (𝓞 (maximalRealSubfield K))) :
        FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv]
  have key : ∀ A : Ideal (𝓞 (maximalRealSubfield K)),
      FractionalIdeal.count K v ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    intro A
    rw [← count_coe_map_conj]
    congr 2
    have : ((ringOfIntegersComplexConj K).toRingEquiv : 𝓞 K →+* 𝓞 K).comp
        (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap _ _ := by
      ext1 x
      exact (ringOfIntegersComplexConj K).commutes x
    conv_lhs => rw [← this, ← Ideal.map_map]
    rfl
  rw [hIJ, hd1, map_mul, map_inv₀, FractionalIdeal.extendedHom_coeIdeal_eq_map,
    FractionalIdeal.extendedHom_coeIdeal_eq_map] at hbI
  have hb0 := b.ne_zero
  rw [hbI] at hb0 ⊢
  rw [FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, key, key]

end KStar.IdealValuations
