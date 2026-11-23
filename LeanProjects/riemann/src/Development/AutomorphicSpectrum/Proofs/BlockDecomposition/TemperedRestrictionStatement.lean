import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestriction
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_restriction : TempRes := by
  first | exact @GlobalTheory.CompanionTheory.TempRes.tempRes | exact GlobalTheory.CompanionTheory.TempRes.tempRes | (intros; apply GlobalTheory.CompanionTheory.TempRes.tempRes <;> assumption)
