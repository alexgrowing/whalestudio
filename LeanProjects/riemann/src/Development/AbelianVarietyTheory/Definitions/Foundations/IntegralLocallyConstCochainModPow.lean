import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LocallyConstantTwoCochain

noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt p (w g)) ∧ ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong p k (w h) (w g)

def LocallyConstantTwoCochainOn (k : ℕ) (H : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, ∀ h ∈ H, IsInt p (ξ g h)) ∧ ∀ g ∈ H, ∀ h ∈ H, ∃ S : Finset Ω, ∀ g' ∈ H, ∀ h' ∈ H,
    (∀ x ∈ S, g' x = g x ∧ h' x = h x) → Cong p k (ξ g' h') (ξ g h)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong p k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt p x ∧ ∀ g ∈ H, Cong p k (c g) (((χ g).val : Ω) ^ j * g x - x)

def IsTwistedTwoCocycle' (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ t ∈ H,
    Cong p k (((χ g).val : Ω) ^ j * g (ξ h t) + ξ g (h * t)) (ξ (g * h) t + ξ g h)

def IsTwistedTwoCoboundary' (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k H w ∧ ∀ g ∈ H, ∀ h ∈ H,
    Cong p k (ξ g h) (((χ g).val : Ω) ^ j * g (w h) - w (g * h) + w g)

variable (p) in

def plogQ (m k a : ℕ) : ZMod (p ^ k) :=
  ∑ i ∈ Finset.Icc 1 (2 * k + 2), (-1 : ZMod (p ^ k)) ^ (i + 1) *
    (p : ZMod (p ^ k)) ^ (m * (i - 1) - padicValNat p i) *
    ((i / p ^ padicValNat p i : ℕ) : ZMod (p ^ k))⁻¹ * (a : ZMod (p ^ k)) ^ i

def IsLam (T : Tower p Ω) (m k : ℕ) (H : Subgroup (Gal p Ω)) (lam : Gal p Ω → ZMod (p ^ k)) : Prop :=
  1 ≤ m ∧ ∃ a : Gal p Ω → ZMod (p ^ k), IsKum T k H (T.ζ (m + k)) a ∧ ∀ g ∈ H, lam g = plogQ p m k (a g).val

end GlobalTheory.K5
