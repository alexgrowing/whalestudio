import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingIntegral_jointHarmonic_pos : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X := by
  first | exact @GlobalTheory.DoublingPos.doubling_pos | exact GlobalTheory.DoublingPos.doubling_pos | (intros; apply GlobalTheory.DoublingPos.doubling_pos <;> assumption)
