import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by
  first | exact @GlobalTheory.NormUnits.norm_onto_units | exact GlobalTheory.NormUnits.norm_onto_units | (intros; apply GlobalTheory.NormUnits.norm_onto_units <;> assumption)
