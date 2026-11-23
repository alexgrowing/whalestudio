import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDR_of_allSteps_hold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), (∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z') → HasDR Z' := by
  first | exact @GlobalTheory.LocM.StepFrame.hasDR_of_allSteps | exact GlobalTheory.LocM.StepFrame.hasDR_of_allSteps | (intros; apply GlobalTheory.LocM.StepFrame.hasDR_of_allSteps <;> assumption)
