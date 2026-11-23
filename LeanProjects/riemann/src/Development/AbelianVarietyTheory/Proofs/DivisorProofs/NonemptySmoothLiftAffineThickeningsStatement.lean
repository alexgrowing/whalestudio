import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickenings
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_smoothLiftAffineThickenings : ∀ D : Data, Nonempty (Lift D) := by
  first | exact @GlobalTheory.SmoothLift.LiftEx.nonempty_lift | exact GlobalTheory.SmoothLift.LiftEx.nonempty_lift | (intros; apply GlobalTheory.SmoothLift.LiftEx.nonempty_lift <;> assumption)
