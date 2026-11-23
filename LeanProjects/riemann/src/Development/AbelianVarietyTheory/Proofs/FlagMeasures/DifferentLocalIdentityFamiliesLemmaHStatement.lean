import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentLocalIdentity_familiesLemmaH : Formalism.L2.SG.FamDefs.HTie := by
  first | exact @GlobalTheory.HTieLeaf.main | exact GlobalTheory.HTieLeaf.main | (intros; apply GlobalTheory.HTieLeaf.main <;> assumption)
