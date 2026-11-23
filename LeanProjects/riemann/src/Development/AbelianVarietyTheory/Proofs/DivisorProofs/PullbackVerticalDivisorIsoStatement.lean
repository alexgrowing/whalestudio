import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackVerticalDivisorIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_vertical_divisor_iso : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (I : B.effVert), Nonempty ((Scheme.Modules.pullback f.f).obj (divMod I.1) ≅ divMod (GlobalTheory.Vert.Model.effPull f.comp_str I).1) := by
  first | exact @GlobalTheory.DivPullStr.main | exact GlobalTheory.DivPullStr.main | (intros; apply GlobalTheory.DivPullStr.main <;> assumption)
