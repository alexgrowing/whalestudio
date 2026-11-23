import Mathlib

namespace PI.PadicCongruence

variable {R : Type*} [CommRing R] (S : Subring R) (p : ℕ)

def ModP (x y : R) : Prop := ∃ z ∈ S, x = y + (p : R) * z

theorem ModP.trans {x y w : R} (h1 : ModP S p x y) (h2 : ModP S p y w) : ModP S p x w := by
  obtain ⟨z1, hz1, rfl⟩ := h1
  obtain ⟨z2, hz2, rfl⟩ := h2
  exact ⟨z2 + z1, S.add_mem hz2 hz1, by ring⟩

theorem ModP.add {x y x' y' : R} (h : ModP S p x y) (h' : ModP S p x' y') : ModP S p (x + x') (y + y') := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', rfl⟩ := h'
  exact ⟨z + z', S.add_mem hz hz', by ring⟩

end PI.PadicCongruence
