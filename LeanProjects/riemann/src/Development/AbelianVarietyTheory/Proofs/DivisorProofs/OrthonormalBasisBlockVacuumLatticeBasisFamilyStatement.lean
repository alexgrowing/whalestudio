import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBasis_blockVacuumLatticeBasisFamily : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), StandardLatticesGL3.OnB D (bas B n n') := by
  first | exact @GlobalTheory.BaseVacuum.onB_bas | exact GlobalTheory.BaseVacuum.onB_bas | (intros; apply GlobalTheory.BaseVacuum.onB_bas <;> assumption)
