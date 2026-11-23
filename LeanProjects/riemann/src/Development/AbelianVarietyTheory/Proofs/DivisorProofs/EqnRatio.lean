import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo

namespace GlobalTheory.HtAdd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}

def eqnRatio (Y : FlagCpt Z e) {ι : Type} (s : Finset ι) (a : ι → Sym E) (n : ι → ℤ) (x : Y.Y.X) : Y.Y.Fnˣ :=
  (∏ i ∈ s, eqn (divOf Y (expo Dw (Finsupp.single (a i) 1))) x ^ n i) *
    (eqn (divOf Y (expo Dw (∑ i ∈ s, Finsupp.single (a i) (n i)))) x)⁻¹

end GlobalTheory.HtAdd
