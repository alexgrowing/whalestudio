import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_add_effective_of_nef_big : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  first | exact @GlobalTheory.exists_ample_add_eff_of_isNef_isBig | exact GlobalTheory.exists_ample_add_eff_of_isNef_isBig | (intros; apply GlobalTheory.exists_ample_add_eff_of_isNef_isBig <;> assumption)
