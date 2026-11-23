import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionMemInducedDegreeOneCharDiff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ), f ∈ D0 E → ind E f ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | exact GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 <;> assumption)
