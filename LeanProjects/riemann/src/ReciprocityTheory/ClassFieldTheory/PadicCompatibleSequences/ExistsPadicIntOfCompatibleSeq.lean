import Mathlib

noncomputable section

namespace ReciprocityTheory.DiscreteGroups.PeuVal

open CategoryTheory

theorem exists_compatible_seq {Y : ℕ → Type*} (T : ∀ r, Set (Y r)) (φ : ∀ r, Y (r + 1) → Y r)
    (hne : ∀ r, (T r).Nonempty) (hfin : ∀ r, (T r).Finite) (hφ : ∀ r, ∀ f ∈ T (r + 1), φ r f ∈ T r) :
    ∃ f : ∀ r, Y r, (∀ r, f r ∈ T r) ∧ ∀ r, φ r (f (r + 1)) = f r := by
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := fun r => ↥(T r))
    (fun r => ↾fun f => ⟨φ r f.1, hφ r f.1 f.2⟩)
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun r => (u ⟨r⟩).1, fun r => (u ⟨r⟩).2, fun r => ?_⟩
  have h := hu (homOfLE (Nat.le_add_right r 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

end ReciprocityTheory.DiscreteGroups.PeuVal
