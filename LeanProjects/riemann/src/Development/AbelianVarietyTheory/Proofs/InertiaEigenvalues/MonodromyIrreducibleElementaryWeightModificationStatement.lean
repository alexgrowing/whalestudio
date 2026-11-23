import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_irreducible_elementary_weightModification : ModStep := by
  first | exact @GlobalTheory.PMon.modStep_holds | exact GlobalTheory.PMon.modStep_holds | (intros; apply GlobalTheory.PMon.modStep_holds <;> assumption)
