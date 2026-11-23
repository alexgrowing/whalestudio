import Mathlib
open NumberField

namespace GlobalTheory

theorem absNorm_map_ringOfIntegers_hom (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)) :
    Module.finrank ℚ E ∣ Module.finrank ℚ K ∧
      Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  have hτinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [eq_intCast, map_intCast]
    constructor
    · intro h
      have : ((n : 𝓞 K) : K) = 0 := by rw [h]; rfl
      exact_mod_cast this
    · rintro rfl; simp
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp hτinj
  let φ : E →+* K := IsFractionRing.lift hinj
  letI : Algebra E K := φ.toAlgebra
  have hmap : τ = algebraMap (𝓞 E) (𝓞 K) := by
    ext x
    change ((algebraMap (𝓞 K) K).comp τ) x = φ (algebraMap (𝓞 E) E x)
    rw [IsFractionRing.lift_algebraMap]
  have htower := Module.finrank_mul_finrank ℚ E K
  have hE : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨⟨Module.finrank E K, htower.symm⟩, ?_⟩
  have hq : Module.finrank ℚ K / Module.finrank ℚ E = Module.finrank E K := by
    rw [← htower, Nat.mul_div_cancel_left _ hE]
  rw [hq, hmap, Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) 𝔞,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K]

end GlobalTheory
