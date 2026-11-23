import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegrees
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_restriction_bijective_low_degrees : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | exact GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | (intros; apply GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo <;> assumption)
