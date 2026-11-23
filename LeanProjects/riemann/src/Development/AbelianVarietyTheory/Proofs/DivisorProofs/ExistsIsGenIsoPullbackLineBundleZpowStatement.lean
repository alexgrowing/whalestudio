import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpow
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ, ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen := by
  first | exact @GlobalTheory.PullPow.exists_isGen_iso_pw | exact GlobalTheory.PullPow.exists_isGen_iso_pw | (intros; apply GlobalTheory.PullPow.exists_isGen_iso_pw <;> assumption)
