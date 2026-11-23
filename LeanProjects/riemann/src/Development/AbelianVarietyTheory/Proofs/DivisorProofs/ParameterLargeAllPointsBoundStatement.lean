import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_large_all_points_bound : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Large := by
  first | exact @GlobalTheory.ExpTie.parOf_large | exact GlobalTheory.ExpTie.parOf_large | (intros; apply GlobalTheory.ExpTie.parOf_large <;> assumption)
