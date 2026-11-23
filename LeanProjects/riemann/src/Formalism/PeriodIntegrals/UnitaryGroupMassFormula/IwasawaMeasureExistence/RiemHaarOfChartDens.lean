import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.KGauge

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

section Ratio

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

end Ratio

variable {n : ℕ} {ε : Fin n → Bool}

def haarH (H : Subgroup (Formalism.REAL.UJ ε)) (hc : IsClosed (H : Set (Formalism.REAL.UJ ε))) : Measure (Formalism.REAL.UJ ε) :=
  haveI : LocallyCompactSpace H := hc.locallyCompactSpace
  haveI : BorelSpace H := Subtype.borelSpace _
  (Measure.haar : Measure H).map Subtype.val

def ChartDens : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε)
    (hc : IsClosed (H : Set (Formalism.REAL.UJ ε))),
    ∃ δ : ℝ, 0 < δ ∧ ∃ (j : lieSp (conjInv H y) → ℝ≥0∞) (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto j (𝓝 0) (𝓝 c) ∧
      ∀ T : Set (lieSp (conjInv H y)), MeasurableSet T → T ⊆ ball 0 δ →
        haarH H hc (expSetY H y T) = ∫⁻ x in T, j x

end PI.IwaMeasEx.Gauge.ZetaZeros

end
