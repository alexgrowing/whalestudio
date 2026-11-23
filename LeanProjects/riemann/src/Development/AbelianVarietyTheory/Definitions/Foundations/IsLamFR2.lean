import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def IsLamFR2 (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (χ : ℕ → ℤ_[l]) (j : Ω →+* Qbar l)
    (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  (∀ d : ℕ, Nat.Coprime d N → ∀ b ∈ X.B N l w, pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    IsLamFR X A N w χ j pr c lam

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {χ : ℕ → ℤ_[l]} {j : Ω →+* Qbar l}
  {pr : X.Fn l → Fin 2 → Qbar l} {c : Coef l} {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

theorem IsLamFR2.diam (h : IsLamFR2 X A N w χ j pr c lam) {d : ℕ} (hd : Nat.Coprime d N) {b : X.Fn l}
    (hb : b ∈ X.B N l w) : pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b := h.1 d hd b hb

end Induced

end GlobalTheory.KummerEisensteinGalois

end
