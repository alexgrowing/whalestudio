import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

open MeasureTheory

namespace GlobalTheory.ConjugationEquivalence

def conjEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * u * b⁻¹, (h u).1 u.2⟩
  invFun u := ⟨b⁻¹ * u * b, (h _).2 (by simpa [mul_assoc] using u.2)⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

end GlobalTheory.ConjugationEquivalence
