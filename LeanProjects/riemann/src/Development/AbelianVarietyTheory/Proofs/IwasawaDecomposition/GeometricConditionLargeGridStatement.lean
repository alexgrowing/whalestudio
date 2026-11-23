import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricConditionLargeGrid
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_condition_large_grid : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR (NEa hL N (GridA CF)) S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR (NEa hL N (GridA CF)) S Γ) RL.Row_tie → RL.At (prmR (NEa hL N (GridA CF)) S Γ) fun Q L => RL.GeometricBoundCondition Q L CF := by
  first | exact @GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA | exact GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA | (intros; apply GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA <;> assumption)
