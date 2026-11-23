import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_semidefinite_null_radical : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ x, (B x x).re = 0 → ∀ w, B x w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | exact GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | (intros; apply GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic <;> assumption)
