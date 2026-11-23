import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_complexPoints_open_variety : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ) (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) := by
  first | exact @GlobalTheory.CxConn.isPreconnected_ptsIn | exact GlobalTheory.CxConn.isPreconnected_ptsIn | (intros; apply GlobalTheory.CxConn.isPreconnected_ptsIn <;> assumption)
