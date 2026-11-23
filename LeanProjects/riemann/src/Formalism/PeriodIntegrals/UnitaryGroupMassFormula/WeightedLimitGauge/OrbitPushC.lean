import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def hq (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : (Fin k → ℂ) × ℂ :=
  (y, (Real.sqrt (∑ i, Complex.normSq (y i) + T') : ℂ) * Complex.exp (θ * Complex.I))

def hqI (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ y, E.indicator 1 (hq k T' y θ)

def HypTh : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = c * hqI k T' E

def ConeVol : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → volume (coneSh k T' E) = c * hqI k T' E

theorem coneForm_of (hH : HypTh) (hV : ConeVol) : ConeForm := by
  intro k T' hT'
  obtain ⟨c1, h10, h1t, h1⟩ := hH k T' hT'
  obtain ⟨c2, h20, h2t, h2⟩ := hV k T' hT'
  refine ⟨c1 / c2, ENNReal.div_pos h10 h2t |>.ne', ENNReal.div_ne_top h1t h20, fun E hE => ?_⟩
  rw [h1 E hE, h2 E hE, ← mul_assoc, ENNReal.div_mul_cancel h20 h2t]

end PI.RhsWLim.W
