import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift : (∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res1 k w) ∧ (∀ w, ∃! k, Λ.Res1 k w) ∧ ∀ k w, Λ.Res1 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z1 ↔ w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D0 g = k) ↔ ∃ g, dTot0 (OAff D.s) g = w)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res2 k w) ∧ (∀ w, ∃! k, Λ.Res2 k w) ∧ ∀ k w, Λ.Res2 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z2 ↔ w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D1 g = k) ↔ ∃ g, dTot1 (OAff D.s) g = w) := by
  first | exact @GlobalTheory.PDForm.lift_res_bij | exact GlobalTheory.PDForm.lift_res_bij | (intros; apply GlobalTheory.PDForm.lift_res_bij <;> assumption)
