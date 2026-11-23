import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso : ∀ (X : Scheme.{0}) (W : X.Opens) (L M : LB X), LBIso (L.pull W.ι) (M.pull W.ι) → ∃ w : Cmp W L M, IsoOn W L M w := by
  first | exact @GlobalTheory.PicGlue.isoOn_of_lbIso | exact GlobalTheory.PicGlue.isoOn_of_lbIso | (intros; apply GlobalTheory.PicGlue.isoOn_of_lbIso <;> assumption)
