import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentially_semistable_reducible_unramified_split : RedStep := by
  first | exact @GlobalTheory.PMon.Red.redStep | exact GlobalTheory.PMon.Red.redStep | (intros; apply GlobalTheory.PMon.Red.redStep <;> assumption)
