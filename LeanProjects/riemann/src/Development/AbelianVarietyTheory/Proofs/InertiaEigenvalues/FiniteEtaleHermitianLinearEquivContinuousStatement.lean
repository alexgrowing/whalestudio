import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), Continuous j ∧ Continuous j.symm := by
  first | exact @GlobalTheory.JR.et_equiv_continuous | exact GlobalTheory.JR.et_equiv_continuous | (intros; apply GlobalTheory.JR.et_equiv_continuous <;> assumption)
