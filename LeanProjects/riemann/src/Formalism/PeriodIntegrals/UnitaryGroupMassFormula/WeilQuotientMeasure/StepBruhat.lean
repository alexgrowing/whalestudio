import Mathlib
import Formalism.PeriodIntegrals.WeilQuotMeas

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

def StepBruhat : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ g : G, ∫⁻ h, β (g * (h : G)) ∂ν = 1

def StepInvInv : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K),
    ν.IsHaarMeasure → ν.IsMulRightInvariant → ν.IsInvInvariant

end PI.WeilQuotMeas.UnitaryGroupMassFormula
