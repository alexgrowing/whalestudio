import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homGlue_pt_ext_of_openCover : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (y y' : HomGlue.Pt A B L M Z), (∀ i, y.map hL hM (𝒰.f i) = y'.map hL hM (𝒰.f i)) → y = y' := by
  first | exact @GlobalTheory.EndLoc.HomGlue.Pt.ext_cover | exact GlobalTheory.EndLoc.HomGlue.Pt.ext_cover | (intros; apply GlobalTheory.EndLoc.HomGlue.Pt.ext_cover; all_goals assumption)
