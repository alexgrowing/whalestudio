import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  first | exact @GlobalTheory.JR.gammaOne_holds | exact GlobalTheory.JR.gammaOne_holds | (intros; apply GlobalTheory.JR.gammaOne_holds <;> assumption)
