import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK → ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  first | exact @GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | exact GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | (intros; apply GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB <;> assumption)
