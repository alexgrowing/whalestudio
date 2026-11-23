import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TypePOfLargeGapDiscreteSeriesBessel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  first | exact @GlobalTheory.TypeAsm.TopGap.typeBound_of_gap | exact GlobalTheory.TypeAsm.TopGap.typeBound_of_gap | (intros; apply GlobalTheory.TypeAsm.TopGap.typeBound_of_gap <;> assumption)
