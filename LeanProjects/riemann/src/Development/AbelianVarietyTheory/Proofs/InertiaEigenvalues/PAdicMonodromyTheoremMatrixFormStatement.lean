import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  first | exact @GlobalTheory.PMon.matThm_holds | exact GlobalTheory.PMon.matThm_holds | (intros; apply GlobalTheory.PMon.matThm_holds <;> assumption)
