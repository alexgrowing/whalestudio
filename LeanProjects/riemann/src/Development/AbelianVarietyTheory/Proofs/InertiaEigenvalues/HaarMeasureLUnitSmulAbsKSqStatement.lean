import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_L_unit_smul_absK_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  first | exact @GlobalTheory.JR.ScaleHaarL.main | exact GlobalTheory.JR.ScaleHaarL.main | (intros; apply GlobalTheory.JR.ScaleHaarL.main <;> assumption)
