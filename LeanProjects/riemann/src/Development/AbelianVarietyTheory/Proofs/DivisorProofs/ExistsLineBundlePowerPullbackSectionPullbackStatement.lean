import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerPullbackSectionPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ) (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι, s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q) (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  first | (exact @GlobalTheory.HomFixMat.pullSec_exists) | (exact GlobalTheory.HomFixMat.pullSec_exists) | (intros; apply GlobalTheory.HomFixMat.pullSec_exists  <;> assumption)
