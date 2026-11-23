import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace PositivityTheory.S2.Clozel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def EopV (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ π.V :=
  (1 / 2 : ℂ) • (π.op (.lie (toL (Matrix.single i j (atEmb τ 1)))) -
    Complex.I • π.op (.lie (toL (Matrix.single i j (atEmb τ Complex.I)))))

def IsHerm (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ (X : Lie E a) (φ ψ : π.V), B (π.op (.lie X) φ) ψ = -B φ (π.op (.lie X) ψ)) ∧ ∃ φ : π.V, B φ φ ≠ 0

end PositivityTheory.S2.Clozel

end
