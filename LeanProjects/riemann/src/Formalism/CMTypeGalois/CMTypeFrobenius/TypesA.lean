import Mathlib
import Formalism.CMTypeGalois.StatementGroup

open Finset

namespace Formalism.Q3

section general

variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

lemma cc_mul (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]

lemma mem_dualTypeG (hc : c * c = 1) (Φ : Finset G) (g : G) :
    g ∈ dualTypeG c Φ ↔ g = 1 ∨ (c * g ∈ Φ ∧ c * g ≠ 1) := by
  unfold dualTypeG
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · rw [Finset.mem_erase] at ha
      rw [cc_mul hc]
      exact Or.inr ⟨ha.2, ha.1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c * g, Finset.mem_erase.2 ⟨h2, h1⟩, cc_mul hc g⟩

lemma mul_ne_one_iff' (hc : c * c = 1) (g : G) : c * g ≠ 1 ↔ g ≠ c := by
  constructor
  · rintro h rfl
    exact h hc
  · intro h h'
    apply h
    have := cc_mul hc g
    rw [h', mul_one] at this
    exact this.symm

lemma key_dual (hc : c * c = 1) {Φ : Finset G} (hΦ : IsCMTypeG c Φ) (σ : G) (h1 : σ ≠ 1)
    (h2 : σ ≠ c) : σ ∈ dualTypeG c Φ ↔ σ ∉ Φ := by
  rw [mem_dualTypeG hc, hΦ σ, not_not]
  have := (mul_ne_one_iff' hc σ).2 h2
  tauto

end general

end Formalism.Q3
