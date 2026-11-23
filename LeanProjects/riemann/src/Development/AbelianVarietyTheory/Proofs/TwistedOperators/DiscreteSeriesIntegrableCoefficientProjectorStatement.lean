import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjector
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_integrableCoefficient_projector : ∀ X : ProvA, DiscreteSeriesPositivity X → CoverHaarIntegration X → DiscreteSeriesHighestVector X := by
  first | exact @GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | exact GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | (intros; apply GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity <;> assumption)
