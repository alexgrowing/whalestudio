import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε), qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → ∀ b : Formalism.REAL.UJ ε → ENNReal, Measurable b → (∀ g, ENNReal.ofReal c' * ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) → ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (2 ^ (n + 1) * gaussDens ε (sgn ℝ s)) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_quotient | exact GlobalTheory.GaugeQuot.gauge_quotient | (intros; apply GlobalTheory.GaugeQuot.gauge_quotient <;> assumption)
