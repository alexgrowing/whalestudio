import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_prime_pow_torsionFree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ), l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n → (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  first | exact @GlobalTheory.principalCongruence_torsionFree | exact GlobalTheory.principalCongruence_torsionFree | (intros; apply GlobalTheory.principalCongruence_torsionFree; all_goals assumption)
