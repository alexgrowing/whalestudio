import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allSteps_hold_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), HasDR Z' → (∃ f, IsMap Z' Z f) → ∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z' := by
  first | exact @GlobalTheory.LocM.StepOfFrame.holds_of_hasDR | exact GlobalTheory.LocM.StepOfFrame.holds_of_hasDR | (intros; apply GlobalTheory.LocM.StepOfFrame.holds_of_hasDR <;> assumption)
