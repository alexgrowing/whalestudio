import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_mem_iff_not_unit_localization : ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T), t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem <;> assumption)
