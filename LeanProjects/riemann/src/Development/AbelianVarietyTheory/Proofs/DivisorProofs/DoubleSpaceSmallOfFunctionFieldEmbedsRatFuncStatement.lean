import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFunc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  first | exact @GlobalTheory.FlagPush.SmallPf.main | exact GlobalTheory.FlagPush.SmallPf.main | (intros; apply GlobalTheory.FlagPush.SmallPf.main <;> assumption)
