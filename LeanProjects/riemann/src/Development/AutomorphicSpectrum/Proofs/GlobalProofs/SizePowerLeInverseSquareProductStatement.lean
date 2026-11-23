import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProduct
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_power_le_inverse_square_product : ∀ (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ), n * B + 2 ≤ N → (∀ i, cs.count i = N ∨ m i = 0) →
  sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq <;> assumption)
