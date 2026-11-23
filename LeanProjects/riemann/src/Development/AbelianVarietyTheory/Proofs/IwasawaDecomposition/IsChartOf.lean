import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorRef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

def IsChartOf (Z : GMod Xo c) {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (a : 𝓞 c.F)
    (b : 𝓞 c.F →+* R) (u : C.X ⟶ Z.X) : Prop :=
  IsOpenImmersion u ∧ u ≫ Z.s = C.s ≫ spMap b ∧
    Set.range u = Z.s ⁻¹' {x : Sp (𝓞 c.F) | a ∉ x.asIdeal} ∧ C.j ≫ u = Z.j ∧ Nonempty (SABMap C.t Z.t u)

end GlobalTheory.TorRef
