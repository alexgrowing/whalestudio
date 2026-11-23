import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Covolume

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module ZSpan NumberField

noncomputable section

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]

omit [MeasurableSpace V] [BorelSpace V] in

theorem finite_lattice_closedBall (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : V) r)
    (s := (L : Set V)) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩

variable [IsZLattice ℝ L]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [DiscreteTopology L] [IsZLattice ℝ L] in

theorem encard_vadd_mem_le (x : V) :
    {g : L | g +ᵥ x ∈ closedBall (0 : V) (1 / 2)}.encard ≤
      {y : V | y ∈ L ∧ ‖y‖ ≤ 1}.encard := by
  rcases Set.eq_empty_or_nonempty {g : L | g +ᵥ x ∈ closedBall (0 : V) (1 / 2)} with hA | ⟨g₀, hg₀⟩
  · rw [hA, Set.encard_empty]
    exact bot_le
  refine Set.encard_le_encard_of_injOn (f := fun g : L ↦ ((g - g₀ : L) : V)) ?_ ?_
  · intro g hg
    refine ⟨(g - g₀).2, ?_⟩
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_zero_right, Submodule.vadd_def,
      vadd_eq_add] at hg hg₀
    have : ((g - g₀ : L) : V) = ((g : V) + x) - ((g₀ : V) + x) := by
      rw [Submodule.coe_sub]; abel
    show ‖((g - g₀ : L) : V)‖ ≤ 1
    rw [this]
    calc ‖((g : V) + x) - ((g₀ : V) + x)‖ ≤ ‖(g : V) + x‖ + ‖(g₀ : V) + x‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hg hg₀
      _ = 1 := by norm_num
  · intro g _ g' _ hgg'
    have := Subtype.val_injective hgg'
    simpa using this

end Euclidean

section Bundle

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

end Bundle

end

end GroundTheory.Heights₂.Heights
