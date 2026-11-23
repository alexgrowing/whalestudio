import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRepUniversal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_pt_of_isGrpPullback : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧ ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  first | exact @GlobalTheory.EndLoc.HomGlue.localRep_universal | exact GlobalTheory.EndLoc.HomGlue.localRep_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.localRep_universal; all_goals assumption)
