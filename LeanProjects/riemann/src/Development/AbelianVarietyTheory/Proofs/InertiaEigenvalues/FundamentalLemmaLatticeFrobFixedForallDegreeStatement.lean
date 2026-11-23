import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree : ∀ r : ℕ, FLAt r := by
  first | exact @GlobalTheory.PMon.flAt_all | exact GlobalTheory.PMon.flAt_all | (intros; apply GlobalTheory.PMon.flAt_all <;> assumption)
