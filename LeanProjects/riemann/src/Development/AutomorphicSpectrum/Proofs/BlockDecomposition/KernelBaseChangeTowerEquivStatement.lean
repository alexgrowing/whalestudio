import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquiv
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_base_change_tower_equiv : ∀ (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P), Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower <;> assumption)
