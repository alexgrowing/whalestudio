import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeEqComapStandardLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockVacuumLattice_eq_comap_standardLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') = (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  first | exact @GlobalTheory.BaseVacuum.laB_eq_comap | exact GlobalTheory.BaseVacuum.laB_eq_comap | (intros; apply GlobalTheory.BaseVacuum.laB_eq_comap <;> assumption)
