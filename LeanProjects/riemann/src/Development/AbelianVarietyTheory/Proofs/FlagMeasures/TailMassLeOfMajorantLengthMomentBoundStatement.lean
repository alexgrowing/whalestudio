import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_mass_le_of_majorantLengthMomentBound : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  first | exact @GlobalTheory.Amp.Cheb.tail_mass_le | exact GlobalTheory.Amp.Cheb.tail_mass_le | (intros; apply GlobalTheory.Amp.Cheb.tail_mass_le <;> assumption)
