import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.NablaSpanC

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

def ProjZ : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 : ℕ) (nu : Lt → YoungDiagram),
    ∃ T : MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      (∀ P, T P ∈ Submodule.span ℤ (Set.range (nablaX N0 nu))) ∧ ∀ J, T (nablaX N0 nu J) = nablaX N0 nu J

end GenFrameSpan
