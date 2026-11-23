import Mathlib

open NumberField

namespace PI

def LocBasisPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), L.FG → Submodule.span E (L : Set (Fin N → E)) = ⊤ →
    ∃ P : Matrix (Fin N) (Fin N) E, P.det ≠ 0 ∧
      (∀ a, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, s • x = ∑ a, c a • P.transpose a

end PI
