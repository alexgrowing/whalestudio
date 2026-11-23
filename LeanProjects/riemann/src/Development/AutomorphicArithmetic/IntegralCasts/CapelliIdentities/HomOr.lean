import Mathlib

namespace UpperTheory.Reformulated.B.Qk44

theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) :
    (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_cases hg : ∀ s ∈ I, f s = g s
  · exact Or.inl hg
  · right
    obtain ⟨a, ha⟩ := not_forall.mp hg
    obtain ⟨haI, hne⟩ := Classical.not_imp.mp ha
    have hah : f a = h a := (H a haI).resolve_left hne
    intro b hbI
    rcases H b hbI with hb | hb
    · rcases H (a * b) (I.mul_mem haI hbI) with hab | hab
      · rw [map_mul, map_mul, hb] at hab
        exact absurd (mul_right_cancel hab) hne
      · rw [map_mul, map_mul, hah] at hab
        exact mul_left_cancel hab
    · exact hb

end UpperTheory.Reformulated.B.Qk44
