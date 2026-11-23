import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_hypothesis_all_points : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @GlobalTheory.ExpTie.parOf_hyp | exact GlobalTheory.ExpTie.parOf_hyp | (intros; apply GlobalTheory.ExpTie.parOf_hyp <;> assumption)
