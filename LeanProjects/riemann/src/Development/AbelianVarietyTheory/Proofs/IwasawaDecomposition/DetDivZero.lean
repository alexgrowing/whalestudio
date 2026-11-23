import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam

namespace GlobalTheory.FlagAmple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Step (Dw : Datum H) : Type := Σ τ : E →+* ℂ, {i : Fin (Dw.mult τ) // 0 < (i : ℕ)}

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

def detDiv (C : FlagCpt Z e) (τ : E →+* ℂ) (i : ℕ) : C.Y.Dv :=
  ∑ a : Fin (Dw.mult τ), if (a : ℕ) < i then C.gr τ a else 0

end GlobalTheory.FlagAmple
