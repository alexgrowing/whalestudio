import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeBasisCoordinateEqCoordinateEqu
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockVacuum_latticeBasis_coordinate_eq_coordinateEquiv : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) := by
  first | exact @GlobalTheory.BaseVacuum.coordB_bas_eq_phi | exact GlobalTheory.BaseVacuum.coordB_bas_eq_phi | (intros; apply GlobalTheory.BaseVacuum.coordB_bas_eq_phi <;> assumption)
