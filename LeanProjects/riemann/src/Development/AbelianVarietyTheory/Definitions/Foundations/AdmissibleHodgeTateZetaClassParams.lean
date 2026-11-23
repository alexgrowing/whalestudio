import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.LambdaValuationPowers

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def AdmissibleHodgeTateZetaClassParams {l : ℕ} [Fact l.Prime] (e : ℕ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (α : Qbar l) : Prop :=
  5 ≤ N ∧ Nat.Coprime l N ∧
    (∀ r₀ : (ZMod l)ˣ, gm r₀ ∈ CongruenceSubgroup.Gamma1 N ∧
      (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = -(r₀ : ZMod l) * (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod l)) ∧
    ‖α‖ = 1 ∧ ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = α • pr b

example {l : ℕ} [Fact l.Prime] (e : ℕ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (gm : (ZMod l)ˣ → SL(2, ℤ)) (α : Qbar l) :
    ¬ AdmissibleHodgeTateZetaClassParams e X pr 4 gm α := fun h => by have := h.1; omega

end GlobalTheory.LambdaValuationPowers
