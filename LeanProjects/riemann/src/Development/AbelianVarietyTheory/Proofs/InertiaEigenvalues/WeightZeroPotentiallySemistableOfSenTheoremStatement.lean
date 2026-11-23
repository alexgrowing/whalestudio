import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheorem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem : SenStep := by
  first | exact @GlobalTheory.PMon.senStep | exact GlobalTheory.PMon.senStep | (intros; apply GlobalTheory.PMon.senStep <;> assumption)
