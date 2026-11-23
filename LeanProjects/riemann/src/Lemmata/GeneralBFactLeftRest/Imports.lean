import Mathlib

open NumberField Module

namespace Bl.general_b_fact_left_rest

theorem goal1 {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  show Nat.card (G ⧸ N) = Nat.card T
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift f ?_) ⟨?_, ?_⟩)
  · intro a b h
    exact (hf a b).2 (QuotientGroup.leftRel_apply.mp h)
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr ((hf a b).1 h)
  · intro t
    obtain ⟨a, rfl⟩ := hs t
    exact ⟨(a : G ⧸ N), rfl⟩

end Bl.general_b_fact_left_rest
