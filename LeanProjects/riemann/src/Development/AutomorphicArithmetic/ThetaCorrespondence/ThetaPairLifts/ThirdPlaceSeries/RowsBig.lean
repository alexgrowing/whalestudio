import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem rows_big_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ,
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  refine ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_large_parameter_bound eps (2 * |Fm.Ct| + 2) heps
  refine ⟨max x0 2, fun x hx hle i _ _ _ j => ?_⟩
  have hCt := Fm.Ct_eq x i
  refine ⟨(Fm.L x i).sc.X', x ^ (2 * |Fm.Ct| + 2),
    rows_big_of_largeParameter (Fm.L x i) (Fm.params x hx i) j eps _ x (Fm.L_x x i hx) (Fm.L_eps x i) ?_ ?_
      ((le_max_right _ _).trans hle) (hx0 x ((le_max_left _ _).trans hle))⟩
  · rw [hCt]
    linarith [le_abs_self Fm.Ct]
  · rw [hCt]
    linarith [le_abs_self Fm.Ct, abs_nonneg Fm.Ct]
end GlobalTheory.ExpTie
end
end
