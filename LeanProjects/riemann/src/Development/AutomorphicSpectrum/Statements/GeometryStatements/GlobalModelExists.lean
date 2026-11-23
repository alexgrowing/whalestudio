import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GlobalModelExists : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)),
    IsGlobal Xo l c Y ∧ GlobalTheory.CompanionTheory.Ar.SplitComps Y ∧ Nonempty Y.X ∧ 1 ≤ D.p ∧ 1 ≤ D.q

end GlobalTheory.CompanionTheory.Ar.Top
