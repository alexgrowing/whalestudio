import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubinTateTwistTotalWeightZero_proof : TwistStep := by
  first | exact @GlobalTheory.PMon.twistStep | exact GlobalTheory.PMon.twistStep | (intros; apply GlobalTheory.PMon.twistStep <;> assumption)
