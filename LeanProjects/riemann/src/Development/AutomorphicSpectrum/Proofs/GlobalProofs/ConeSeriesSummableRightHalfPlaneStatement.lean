import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlane
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_summable_right_half_plane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re → Summable (coneTerm a b s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable <;> assumption)
