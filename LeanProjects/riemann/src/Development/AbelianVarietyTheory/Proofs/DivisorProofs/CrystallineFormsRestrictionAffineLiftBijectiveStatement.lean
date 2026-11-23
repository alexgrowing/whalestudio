import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormsRestrictionAffineLiftBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineForms_restriction_affineLift_bijective : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (h : ∀ U, LevE D.κ D.t D.i (n + 1) (Λ.toE.obj U)), ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i (n + 1)).ι).resMap ((LevE D.κ D.t D.i (n + 1)).lift Λ.toE h)).Bij := by
  first | exact @GlobalTheory.PDForm.levLift_resMap_bij | exact GlobalTheory.PDForm.levLift_resMap_bij | (intros; apply GlobalTheory.PDForm.levLift_resMap_bij <;> assumption)
