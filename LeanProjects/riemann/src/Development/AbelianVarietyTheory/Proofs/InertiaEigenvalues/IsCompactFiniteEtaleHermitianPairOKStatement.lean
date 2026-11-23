import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactFiniteEtaleHermitianPairOK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  first | exact @GlobalTheory.JR.OKCompact.okCompact | exact GlobalTheory.JR.OKCompact.okCompact | (intros; apply GlobalTheory.JR.OKCompact.okCompact <;> assumption)
