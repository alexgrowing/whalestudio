import Mathlib

noncomputable section

namespace PI.ProdUnitInert

open Classical

abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

def lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ Qbar then lam ⟨x, h⟩ else 0

end PI.ProdUnitInert

namespace PI

open PI.ProdUnitInert

def ProdUnitInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (c : E →+* E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E → (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    Module.finrank ℚ K = 2 → ∀ (d p : ℕ) [Fact p.Prime] (b : K), b ^ 2 = ((-(d : ℤ) : ℤ) : K) →
    jacobiSym (-(d : ℤ)) p = -1 → ∀ (lam : Qbar →+* ℂ_[p]) (z : E), z * c z = 1 →
    ‖lamC lam (∏ s, emb s z)‖ = 1

end PI

end
