import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ExistsCoordinate.exists_coord :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {y : E},
    y ∈ ℚ[(↑H.rt : E)] →
      ∃ (u : ℚ) (v : ℚ),
        y =
          (↑u : E) +
            (↑v : E) *
              (↑H.rt :
                E) := by
  intro E _ _ _ H y hy
  have hsq : (H.rt : E) * (H.rt : E) = -(H.d : E) := by
    have h := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) H.rt_sq
    simpa [sq] using h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a * c - b * e * H.d, a * e + b * c, by push_cast; linear_combination (b * e : E) * hsq⟩
