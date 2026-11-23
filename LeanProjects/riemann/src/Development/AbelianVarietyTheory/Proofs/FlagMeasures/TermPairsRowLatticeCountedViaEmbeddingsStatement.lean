import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  first | exact @GlobalTheory.TypeAsm.perRowC | exact GlobalTheory.TypeAsm.perRowC | (intros; apply GlobalTheory.TypeAsm.perRowC <;> assumption)
