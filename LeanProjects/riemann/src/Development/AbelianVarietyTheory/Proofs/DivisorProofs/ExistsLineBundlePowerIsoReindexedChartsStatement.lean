import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerIsoReindexedCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts : ∀ {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂) (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))), w.IsGen → ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  first | (exact @GlobalTheory.PowIsoRe.exists_powIso) | (exact GlobalTheory.PowIsoRe.exists_powIso) | (intros; apply GlobalTheory.PowIsoRe.exists_powIso  <;> assumption)
