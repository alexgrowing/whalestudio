import Mathlib

namespace Bl.SecondBlockLemmaO

theorem goal1 :
  ∀ {V : Type} [inst : CommRing.{0} V] [inst_1 : IsDomain.{0} V] [IsDiscreteValuationRing.{0} V] {ϖ : V},
  Irreducible.{0} ϖ → IsLocalization.Away.{0, 0} ϖ (FractionRing.{0} V) := by
  intro V _ _ _ ϖ hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj := IsFractionRing.injective V (FractionRing V)
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).2 (pow_ne_zero n hϖ0)
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap V (FractionRing V) b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hu' : algebraMap V (FractionRing V) (↑u⁻¹ : V) * algebraMap V (FractionRing V) (↑u : V) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b *
      algebraMap V (FractionRing V) (ϖ ^ n) = algebraMap V (FractionRing V) (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hbK, hu]
    simp only [map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) a * algebraMap V (FractionRing V) ϖ ^ n)) * hu'
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

end Bl.SecondBlockLemmaO
