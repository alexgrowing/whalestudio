import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weil | exact GlobalTheory.JR.fourierMatch_of_weil | (intros; apply GlobalTheory.JR.fourierMatch_of_weil <;> assumption)
