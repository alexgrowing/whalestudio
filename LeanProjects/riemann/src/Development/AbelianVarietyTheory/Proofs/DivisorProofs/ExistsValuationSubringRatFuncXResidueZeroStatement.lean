import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero : ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  first | exact @GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | exact GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | (intros; apply GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero <;> assumption)
