import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearLiftBijectiveLocalization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_lift_bijective_localization : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) → (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧ ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  first | exact @GlobalTheory.DeRham.localisation_of_liftSemi_bijective | exact GlobalTheory.DeRham.localisation_of_liftSemi_bijective | (intros; apply GlobalTheory.DeRham.localisation_of_liftSemi_bijective <;> assumption)
