import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof : PhiCBd := by
  first | exact @GlobalTheory.GoodDepth.ConjPkg.phiCBd | exact GlobalTheory.GoodDepth.ConjPkg.phiCBd | (intros; apply GlobalTheory.GoodDepth.ConjPkg.phiCBd <;> assumption)
