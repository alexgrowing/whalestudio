import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ValPolyLineX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

def FlagPolynomialValue.Statement : Prop :=
  ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) {σ κ : Type} (A : κ → MvPolynomial σ Ω)
    (B : κ → MvPolynomial σ ℂ), (∀ j, ValPoly y z (A j) (B j)) →
    ∀ F : MvPolynomial κ ℤ, ValPoly y z (aeval A F) (aeval B F)

namespace FlagPolynomialValue

open Line

end FlagPolynomialValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
