import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_not_dividing_coprime_ideal_norm : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  first | exact @GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | exact GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | (intros; apply GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top <;> assumption)
