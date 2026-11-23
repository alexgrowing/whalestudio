import Mathlib

noncomputable section

namespace KStar.Tree

variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

def nuOf : ℕ := sInf {k : ℕ | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}

def nuInf : ℕ∞ := ⨅ g, emultiplicity (l : ℤ_[l]) (((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1)

def cyc (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : (Ω ≃ₐ[E] Ω) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω)

end KStar.Tree
