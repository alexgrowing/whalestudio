import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.IsClosedConjInv

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

def LieAdd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (K : Subgroup (Formalism.REAL.UJ ε)), IsClosed (K : Set (Formalism.REAL.UJ ε)) →
    ∀ X ∈ lieOf K, ∀ Y ∈ lieOf K, X + Y ∈ lieOf K

def ChartAt {n : ℕ} {ε : Fin n → Bool} (K : Subgroup (Formalism.REAL.UJ ε)) (δ : ℝ) (W : Set (Formalism.REAL.UJ ε)) : Prop :=
  0 < δ ∧ IsOpen W ∧ (1 : Formalism.REAL.UJ ε) ∈ W ∧
    (∀ x ∈ ball (0 : lieSp K) δ, ∀ x' ∈ ball (0 : lieSp K) δ,
      NormedSpace.exp (toMat ((x : lieSp K) : MatR n)) = NormedSpace.exp (toMat ((x' : lieSp K) : MatR n)) → x = x') ∧
    ∀ g ∈ K, g ∈ W → ∃ x ∈ ball (0 : lieSp K) δ, uMat g = NormedSpace.exp (toMat ((x : lieSp K) : MatR n))

def ChartLoc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (K : Subgroup (Formalism.REAL.UJ ε)), IsClosed (K : Set (Formalism.REAL.UJ ε)) →
    ∀ ρ : ℝ, 0 < ρ → ∃ δ W, δ ≤ ρ ∧ ChartAt K δ W

def LocUniq : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure]
    (W : Set G), IsOpen W → (1 : G) ∈ W → ν W ≠ ⊤ →
    (∀ (x : G) (T : Set G), MeasurableSet T → T ⊆ W → x • T ⊆ W → ν (x • T) = ν T) →
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V ⊆ W ∧ ∃ κ : ℝ≥0∞, κ ≠ ⊤ ∧
      ∀ S : Set G, MeasurableSet S → S ⊆ V → ν S = κ * μ S

def DensChart : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (K : Subgroup (Formalism.REAL.UJ ε)) (hc : IsClosed (K : Set (Formalism.REAL.UJ ε))),
    (∀ X ∈ lieOf K, ∀ Y ∈ lieOf K, X + Y ∈ lieOf K) → (∀ ρ : ℝ, 0 < ρ → ∃ δ W, δ ≤ ρ ∧ ChartAt K δ W) →
    ∃ δ : ℝ, 0 < δ ∧ ∃ (j : lieSp K → ℝ≥0∞) (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto j (𝓝 0) (𝓝 c) ∧
      ∀ T : Set (lieSp K), MeasurableSet T → T ⊆ ball 0 δ → haarH K hc (expSet1 K T) = ∫⁻ x in T, j x

end PI.IwaMeasEx.Gauge.ZetaZeros

end
