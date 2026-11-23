import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Rec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def GeoRead (Rd : Reading Fr h Z) : Prop :=
  letI := Small.cstAlg Or
  ∃ y' : FrPt Xo c RM.Ω, FrMap ({ Rd.φ with commutes' := Rd.φ_cst } : Om Z →ₐ[c.F] RM.Ω) (genFr h Z) y' ∧
    FrBor Rd.t y' Fr.y₀

end GlobalTheory.CompanionTheory.Ar.Plug
