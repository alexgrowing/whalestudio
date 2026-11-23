import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_height_lt_genus : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) := by
  first | exact @GlobalTheory.ExpTie.atPts_h_lt_g | exact GlobalTheory.ExpTie.atPts_h_lt_g | (intros; apply GlobalTheory.ExpTie.atPts_h_lt_g <;> assumption)
