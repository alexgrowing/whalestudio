import Mathlib

open NumberField

namespace PI

namespace DetIdPG

def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i

def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range

end DetIdPG

def DetIdPG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (L L₀ : Submodule (𝓞 E) (Fin N → E)), DetIdPG.IsSDLat E N L → DetIdPG.IsSDLat E N L₀ →
    (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : E) • x ∈ L₀) ∧ ∀ x ∈ L₀, (s : E) • x ∈ L) →
    ∃ (h : ℕ) (z : E), 0 < h ∧ star z * z = 1 ∧ z * star z = 1 ∧ (∀ ψ : E →+* ℂ_[p], ‖ψ z‖ = 1) ∧
      (Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}) ^ h =
        Submodule.span (𝓞 E) {z}

end PI
