import Mathlib

noncomputable section

open MeasureTheory Module
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB

section Scale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

def kI (b : ℝ) : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-b / 2)) ∂μ

end Scale

instance pairBorel (m : ℕ) : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace

instance pairHaar (m : ℕ) : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
