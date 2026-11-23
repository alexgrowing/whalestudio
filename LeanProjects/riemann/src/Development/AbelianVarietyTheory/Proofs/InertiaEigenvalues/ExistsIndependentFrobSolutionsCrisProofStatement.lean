import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsIndependentFrobSolutionsCris_proof : ExI := by
  first | exact @GlobalTheory.PMon.exI_main | exact GlobalTheory.PMon.exI_main | (intros; apply GlobalTheory.PMon.exI_main <;> assumption)
