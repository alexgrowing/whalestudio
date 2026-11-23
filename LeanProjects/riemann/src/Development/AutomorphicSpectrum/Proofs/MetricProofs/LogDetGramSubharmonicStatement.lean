import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_comparable_gram_bound : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | exact GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size <;> assumption)
