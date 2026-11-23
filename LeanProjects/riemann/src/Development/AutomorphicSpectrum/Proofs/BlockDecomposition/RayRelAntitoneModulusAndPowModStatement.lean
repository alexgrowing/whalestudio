import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayRel_antitone_modulus_and_powMod : ∀ (F : Type) [Field F] [NumberField F], (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧ (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | exact GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | (intros; apply GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti <;> assumption)
