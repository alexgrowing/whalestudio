import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.ThetaInValues

theorem brUth_of_laws : Laws → BrUthSt := fun hL _ _ _ _ _ _ _ _ _ _ _ ν =>
  ⟨fun _ _ _ _ hb hb' => weilIs_weil ν hL.globalFns hb hb', fun _ hm hF _ _ hb =>
    ⟨isThetaPt_uth ν hL.globalFns hm hF hb, isCoordPt_uth ν hL.globalFns hm hF hb⟩⟩

end GlobalTheory.ThetaInValues
