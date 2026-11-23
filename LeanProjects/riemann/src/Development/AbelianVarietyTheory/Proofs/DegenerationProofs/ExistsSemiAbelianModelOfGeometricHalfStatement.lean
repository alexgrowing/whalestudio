import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfGeometricHalf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianModel_of_geometricHalf : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ZHGeoSt → ZHSt := by
  first | exact @GlobalTheory.ZH.exists_model_semiAbelian_of_geo | exact GlobalTheory.ZH.exists_model_semiAbelian_of_geo | (intros; apply GlobalTheory.ZH.exists_model_semiAbelian_of_geo <;> assumption)
