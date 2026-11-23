import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlaceDepthBound_proof : NuGoodSt := by
  first | exact @GlobalTheory.GoodDepth.nuGood | exact GlobalTheory.GoodDepth.nuGood | (intros; apply GlobalTheory.GoodDepth.nuGood <;> assumption)
