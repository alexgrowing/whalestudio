import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RealDifferenceConeBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_continuation_from_strips : ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations <;> assumption)
