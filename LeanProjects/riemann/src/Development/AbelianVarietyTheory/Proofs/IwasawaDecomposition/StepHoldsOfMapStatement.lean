import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_holds_of_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (t : Step Y i₀) (Z Z' : Mdl Y i₀), (∃ f, IsMap Z' Z f) → t.Holds Z → t.Holds Z' := by
  first | exact @GlobalTheory.LocM.StepMono.holds_mono | exact GlobalTheory.LocM.StepMono.holds_mono | (intros; apply GlobalTheory.LocM.StepMono.holds_mono <;> assumption)
