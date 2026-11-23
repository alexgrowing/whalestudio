import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSpace_contains_discreteSeriesTensor : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X := by
  first | exact @GlobalTheory.FockTensor.fock_contains_tensor | exact GlobalTheory.FockTensor.fock_contains_tensor | (intros; apply GlobalTheory.FockTensor.fock_contains_tensor <;> assumption)
