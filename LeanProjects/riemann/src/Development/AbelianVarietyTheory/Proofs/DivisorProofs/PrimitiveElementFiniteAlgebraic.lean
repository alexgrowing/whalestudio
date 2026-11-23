import Mathlib
open Polynomial

namespace GlobalTheory

theorem exists_primitive_element_of_isAlgebraic_fin (K C : Type) [Field K] [CharZero K]
    [Field C] [Algebra K C] (m : ℕ) (a : Fin m → C) (ha : ∀ j, IsAlgebraic K (a j)) :
    ∃ α : C, IsAlgebraic K α ∧ ∀ j, a j ∈ IntermediateField.adjoin K {α} := by
  classical
  let E := IntermediateField.adjoin K (Set.range a)
  haveI : FiniteDimensional K E := by
    haveI : Finite (Set.range a) := Set.finite_range a
    exact IntermediateField.finiteDimensional_adjoin (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact (ha j).isIntegral)
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  have hmap := congrArg (IntermediateField.map E.val) hβ
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  refine ⟨E.val β, ((Algebra.IsIntegral.isIntegral (R := K) β).map E.val).isAlgebraic, ?_⟩
  intro j
  rw [hmap]
  rw [IntermediateField.mem_map]
  exact ⟨⟨a j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩, trivial, rfl⟩

end GlobalTheory
