import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferent
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_power_not_dvd_different : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | exact GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | (intros; apply GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different <;> assumption)
