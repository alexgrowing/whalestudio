import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockVacuumCoordinateEquiv_isometry : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)), TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  first | exact @GlobalTheory.BaseVacuum.phi_isom | exact GlobalTheory.BaseVacuum.phi_isom | (intros; apply GlobalTheory.BaseVacuum.phi_isom <;> assumption)
