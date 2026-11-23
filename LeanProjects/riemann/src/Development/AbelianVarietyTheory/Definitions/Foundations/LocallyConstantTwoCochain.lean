import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsCyc (T : Tower p Ω) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k)) : Prop :=
  ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val

def LocallyConstantTwoCochain (k : ℕ) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  (∀ g h, IsInt p (ξ g h)) ∧ ∀ g h, ∃ S : Finset Ω, ∀ g' h' : Gal p Ω,
    (∀ x ∈ S, g' x = g x ∧ h' x = h x) → Cong p k (ξ g' h') (ξ g h)

def IsTwistedTwoCocycleModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ t ∈ H,
    Cong p k (((χ g).val : Ω) * g (ξ h t) + ξ g (h * t)) (ξ (g * h) t + ξ g h)

def IsTwistedTwoCoboundaryModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, LocallyConstantOneCochain k w ∧ ∀ g ∈ H, ∀ h ∈ H,
    Cong p k (ξ g h) (((χ g).val : Ω) * g (w h) - w (g * h) + w g)

end GlobalTheory.K5
