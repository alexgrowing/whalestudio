import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  first | exact @GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | exact GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | (intros; apply GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top <;> assumption)
