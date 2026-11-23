import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def InChi (X : Tower Ω ε) (N w : ℕ) (χ : ℕ → ℤ_[l]) (b : X.Fn l) : Prop :=
  b ∈ X.B N l w ∧ ∀ d : ℕ, Nat.Coprime d N → X.diam N l d b = χ d • b

def IsLamFR (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (χ : ℕ → ℤ_[l]) (j : Ω →+* Qbar l)
    (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧
    ∃ (cL : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n) ∧ FixIc c (per n)) ∧
      ∀ (n : ℕ), cL ≤ n → ∀ (b : X.Fn l), InChi X N w χ b → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
        Cg (n - cL) (lam (seqN 1 j φ)) (per n * pr b 1)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {χ : ℕ → ℤ_[l]} {j : Ω →+* Qbar l}
  {pr : X.Fn l → Fin 2 → Qbar l} {c : Coef l} {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
