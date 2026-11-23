import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_henselian_flat_over_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R') (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | exact GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime | (intros; apply GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime <;> assumption)
