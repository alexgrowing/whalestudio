import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadical
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_psd_isotropic_radical : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | exact GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | (intros; apply GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd <;> assumption)
