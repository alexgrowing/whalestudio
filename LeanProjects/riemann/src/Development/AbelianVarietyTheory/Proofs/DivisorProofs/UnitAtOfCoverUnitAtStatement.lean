import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfCoverUnitAt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitAt_of_cover_unitAt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (g : Y.Fn) (x : Y.X),
    (∀ x' : V.G, V.π x' = x → UnitAt x' (V.φ g)) → UnitAt x g := by
  first | exact @GlobalTheory.unitAt_of_unitAt_φ_cover | exact GlobalTheory.unitAt_of_unitAt_φ_cover | (intros; apply GlobalTheory.unitAt_of_unitAt_φ_cover <;> assumption)
