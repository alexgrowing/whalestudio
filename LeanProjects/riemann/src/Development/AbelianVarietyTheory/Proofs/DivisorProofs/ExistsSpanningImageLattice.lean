import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem image_integral_points_eq_span_of_surjective :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V]
      [Module C V] [Module O V] [IsScalarTower O C V] (h : ℕ) (π : (Fin h → C) →ₗ[C] V),
      Function.Surjective π → ∃ g : Fin h → V, Submodule.span C (Set.range g) = ⊤ ∧
        Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) =
          (Submodule.span O (Set.range g) : Set V) := by
  intro C _ O _ _ V _ _ _ _ h π hπ
  have key : ∀ x : Fin h → C, π x = ∑ i, x i • π (Pi.single i 1) := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  refine ⟨fun i => π (Pi.single i 1), ?_, ?_⟩
  · rw [eq_top_iff]
    rintro v -
    obtain ⟨x, rfl⟩ := hπ v
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨x, (key x).symm⟩
  · ext v
    simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [key]
      simp only [algebraMap_smul]
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [key]
      simp only [algebraMap_smul]

end GlobalTheory
