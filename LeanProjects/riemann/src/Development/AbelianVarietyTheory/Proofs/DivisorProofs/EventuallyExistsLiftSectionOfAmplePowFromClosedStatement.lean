import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  first | exact @GlobalTheory.LiftClosed.eventually_exists_secPull_eq | exact GlobalTheory.LiftClosed.eventually_exists_secPull_eq | (intros; apply GlobalTheory.LiftClosed.eventually_exists_secPull_eq <;> assumption)
