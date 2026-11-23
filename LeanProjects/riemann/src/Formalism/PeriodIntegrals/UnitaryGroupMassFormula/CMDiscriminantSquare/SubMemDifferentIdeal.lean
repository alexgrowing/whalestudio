import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.AdjoinEqTopOfStarNe

open NumberField Polynomial

namespace PIW.CMDiscSq

theorem sub_mem_differentIdeal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) (hne : θ - t ≠ 0) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 E) E
  have hx : star (algebraMap (𝓞 E) E θ) ≠ algebraMap (𝓞 E) E θ := by
    intro h
    apply hne
    rw [sub_eq_zero]
    apply hinj
    rw [ht, h]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ (adjoin_eq_top_of_star_ne hR hx)
  obtain ⟨s, n, hs, hn, hmin⟩ := minpoly_eq_of_star_ne hR hx
  have hAx : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hval : algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) =
      algebraMap (𝓞 E) E (θ - t) := by
    have h1 : aeval (algebraMap (𝓞 E) E θ) (derivative (minpoly F (algebraMap (𝓞 E) E θ))) =
        algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F E hAx, derivative_map,
        aeval_map_algebraMap, aeval_algebraMap_apply]
    rw [← h1, hmin, map_sub, ht]
    simp only [derivative_X_pow, derivative_mul, derivative_C, derivative_X, map_add, map_sub,
      map_mul, map_pow, aeval_X, aeval_C, hs, zero_mul, zero_add, mul_one, add_zero,
      Nat.cast_ofNat, map_ofNat]
    ring
  rw [hinj hval] at hmem
  exact hmem

theorem relDiffTop : RelDiffTop := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨⟨_, _, hP⟩, hR⟩ := hFE
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hP P hPmax
  apply hθt
  apply hle
  apply sub_mem_differentIdeal hR θ t ht
  intro h0
  apply hθt
  rw [h0]
  exact P.zero_mem

end PIW.CMDiscSq
