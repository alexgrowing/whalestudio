import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shintani_cone_domain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain <;> assumption)
