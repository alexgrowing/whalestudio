import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
