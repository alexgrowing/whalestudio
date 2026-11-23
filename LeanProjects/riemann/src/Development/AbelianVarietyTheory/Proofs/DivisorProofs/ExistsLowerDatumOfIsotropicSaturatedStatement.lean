import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lower_datum_of_isotropic_saturated : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  first | exact @GlobalTheory.LowDat.exists_lowerDatum | exact GlobalTheory.LowDat.exists_lowerDatum | (intros; apply GlobalTheory.LowDat.exists_lowerDatum <;> assumption)
