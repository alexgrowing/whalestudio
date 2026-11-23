import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInversePolynomialBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

def MXFacts : Prop :=
  ∀ (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ), vX ∈ UTset r →
    mX k r vX ∈ Nset k r ∧ (∀ p : Fin r → ℂ, mX k r vX *ᵥ xiV k r p = xiV k r (vX *ᵥ p)) ∧
    ∀ w : Fin (2 * r + k + 1) → ℂ, inWb k r w → mX k r vX *ᵥ w = w

def NEFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ ξ : Fin r → ℂ,
    nEich k r z ξ ∈ Nset k r ∧ (∀ p : Fin r → ℂ, nEich k r z ξ *ᵥ xiV k r p = xiV k r p) ∧
    nEich k r z ξ *ᵥ z = z + xiV k r ξ

end PI.PolynomialProperness
