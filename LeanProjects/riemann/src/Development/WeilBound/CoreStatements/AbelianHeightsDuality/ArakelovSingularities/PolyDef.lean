import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

def PolyCovered {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) : Prop :=
  ∃ ξ : X, (∀ y : Sp k, f ξ ⤳ y) ∧ ∀ x : X, ∃ (σ : Type) (_ : Fintype σ) (e : Sp (MvPolynomial σ k) ⟶ X), IsOpenImmersion e ∧
    Fintype.card σ = d ∧ e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k) ∧
    x ∈ Set.range e ∧ ξ ∈ Set.range e

end GlobalTheory.Amb
