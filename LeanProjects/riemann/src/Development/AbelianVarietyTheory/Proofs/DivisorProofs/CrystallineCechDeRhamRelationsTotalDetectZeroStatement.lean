import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧ ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  first | exact @GlobalTheory.PDForm.rel_total_zero | exact GlobalTheory.PDForm.rel_total_zero | (intros; apply GlobalTheory.PDForm.rel_total_zero <;> assumption)
