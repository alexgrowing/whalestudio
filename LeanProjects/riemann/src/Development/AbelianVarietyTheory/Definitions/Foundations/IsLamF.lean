import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenfunctionalZeroProjection
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def IsLamF (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  GlobalTheory.KummerEisensteinGalois.FinSupp lam ∧ (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧
    ∃ (cL : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n) ∧ FixIc c (per n)) ∧
      ∀ (n : ℕ), cL ≤ n → ∀ (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
        Cg (n - cL) (lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j φ)) (per n * pr b 1)

end GlobalTheory.LambdaValuationPowers
