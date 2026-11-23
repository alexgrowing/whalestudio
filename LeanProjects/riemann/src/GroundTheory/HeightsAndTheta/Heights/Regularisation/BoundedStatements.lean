import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

def u (j : Fin B.N) : (Fin D → ℂ) → ℝ := B.chartFun B.ph j

def smoothed (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) : (Fin D → ℂ) → ℝ :=
  molli ρ t (B.u j)

def phReg (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) (x : X) : ℝ :=
  B.smoothed ρ t j (B.chart j x) - B.q j (B.chart j x)

def regularised (ρ : Mollifier D) (t ε : ℝ) (η : Fin B.N → X → ℝ) : X → ℝ :=
  B.glue (fun j x => B.phReg ρ t j x + 4 * ε * η j x) ε

end BoundedPshData

def BoundedChartComparison.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
        |B.phReg ρ t j x - B.phReg ρ t k x| ≤ C / Real.log t⁻¹ + C * t

def BoundedGlue.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D) (η : Fin B.N → X → ℝ) (Cη t ε : ℝ),
    B.IsCutoffFamily η Cη → 0 < t → 0 < ε →
    (∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target) →
    (∀ j k, ∀ x ∈ B.mid j ∩ B.mid k, |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε) →
    A.Smooth (B.regularised ρ t ε η) ∧
      ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ w : Fin D → ℂ,
        -(4 * Cη * ε) * ‖w‖ ^ 2 ≤ levi (B.chartFun (B.regularised ρ t ε η) k) (B.chart k x) w

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Regular
