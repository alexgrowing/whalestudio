import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsNonzeroFrobVectorResidueZero_proof : ExII := by
  first | exact @GlobalTheory.PMon.exII_holds | exact GlobalTheory.PMon.exII_holds | (intros; apply GlobalTheory.PMon.exII_holds <;> assumption)
