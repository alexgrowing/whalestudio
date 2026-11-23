import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

def TwTan {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ) (Y : Model Xo c β)
    (Y' : Model Xo c β') {T : Scheme.{0}} (u₁ : T ⟶ Y.t.G.left) (u₂ : T ⟶ Y'.t.G.left) : Prop :=
  ∃ (u : T ⟶ Y.oF.t.G.left) (u' : T ⟶ Y'.oF.t.G.left), u ≫ Y.m.φ = u₁ ∧ u' ≫ Y'.m.φ = u₂ ∧
    u' ≫ Y'.m0.toSABMap.φ = u ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ ∧
    u' ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u ≫ Y.oF.t.G.hom ≫ pullback.snd _ _

end GlobalTheory.CompanionTheory.Ar
