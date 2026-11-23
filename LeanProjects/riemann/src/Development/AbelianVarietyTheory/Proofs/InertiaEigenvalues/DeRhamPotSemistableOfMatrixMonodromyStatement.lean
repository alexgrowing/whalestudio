import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  first | exact @GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | exact GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | (intros; apply GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm <;> assumption)
