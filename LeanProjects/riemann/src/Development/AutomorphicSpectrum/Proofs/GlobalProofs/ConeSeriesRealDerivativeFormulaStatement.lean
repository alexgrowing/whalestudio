import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormula
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_real_derivative_formula : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) →
  ∀ (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ), (∀ k, 0 ≤ x k) → 0 ≤ τ →
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr <;> assumption)
