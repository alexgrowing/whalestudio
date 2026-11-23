import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def bdDom (R : RegChartData A) (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W j

theorem isOpen_bdDom (R : RegChartData A) (j : Fin R.n) : IsOpen (bdDom R j) :=
  (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j)

def bdEq (R : RegChartData A) (j : Fin R.n) (y : X) : ℂ := ∏ i ∈ R.S j, R.ψ j y i

def bdIdx (R : RegChartData A) (x : X) : Fin R.n := (R.cover x).choose

theorem mem_V''_bdIdx (R : RegChartData A) (x : X) : x ∈ R.V'' (bdIdx R x) :=
  (R.cover x).choose_spec

theorem V''_subset_bdDom (R : RegChartData A) (j : Fin R.n) : R.V'' j ⊆ bdDom R j :=
  fun _ hx => ⟨hx.1, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hx.2)))⟩

theorem mem_bdDom_bdIdx (R : RegChartData A) (x : X) : x ∈ bdDom R (bdIdx R x) :=
  V''_subset_bdDom R _ (mem_V''_bdIdx R x)

def bdPot (R : RegChartData A) (φ : Fin R.n → X → ℝ) (c : ℝ) : LocPot X where
  U x := bdDom R (bdIdx R x)
  isOpen_U _ := isOpen_bdDom R _
  mem_U x := mem_bdDom_bdIdx R x
  φ x y := φ (bdIdx R x) y + c

def bdSec (R : RegChartData A) (x : X) : X → ℂ := bdEq R (bdIdx R x)

def IsBdMetric (R : RegChartData A) (φ : Fin R.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (bdDom R j) (φ j)) ∧
  (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
      A.HoloOn W G ∧ ∀ z ∈ W ∩ (bdDom R j ∩ bdDom R k), φ j z - φ k z = (G z).re) ∧
  ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
    ‖bdEq R j y‖ * Real.exp (-φ j y) = ‖bdEq R k y‖ * Real.exp (-φ k y)

def bdWeight (R : RegChartData A) (χ : Fin R.n → X → ℝ) (g : Fin R.n → Fin R.n → X → ℂ)
    (j : Fin R.n) (y : X) : ℝ :=
  ∑ l, (bdDom R l).indicator (fun z => χ l z * ‖g j l z‖ ^ 2) y

end Objects

def RegYoDense.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A), Dense R.Yo

def RegRCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A),
    ContinuousOn R.r R.Yo

def ChartCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X), IsOpen U →
    (∀ f : X → ℝ, A.SmoothOn U f → ContinuousOn f U) ∧
    ∀ g : X → ℂ, A.HoloOn U g → ContinuousOn g U

def BdEqHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n),
    A.HoloOn (bdDom R j) (bdEq R j) ∧ ∀ y ∈ bdDom R j, (bdEq R j y = 0 ↔ y ∉ R.Yo)

def HyperplaneDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (i : Fin D), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z i = 0 → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = z i * G z

def CoordDivDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (S : Finset (Fin D)), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z ∈ coordDiv S → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = (∏ i ∈ S, z i) * G z

def BdDivides.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ u : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) u ∧ ContinuousOn u (bdDom R j ∩ bdDom R k) ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R k y = u y * bdEq R j y

def BdTransition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ g : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) g ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, g y ≠ 0 ∧ bdEq R j y = g y * bdEq R k y

def BdCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (g : Fin R.n → Fin R.n → X → ℂ), (∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R j y = g j k y * bdEq R k y) →
    ∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y

def BdPartition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ χ : Fin R.n → X → ℝ, (∀ j, A.Smooth (χ j)) ∧ (∀ j y, 0 ≤ χ j y) ∧
      (∀ y, ∑ j, χ j y = 1) ∧ ∀ j, tsupport (χ j) ⊆ bdDom R j

def LogNormHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (W : Set X) (g : X → ℂ),
    IsOpen W → A.HoloOn W g → (∀ y ∈ W, g y ≠ 0) → ∀ y ∈ W, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re

def IndicatorSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U O : Set X) (χ h : X → ℝ),
    IsOpen U → IsOpen O → A.Smooth χ → tsupport χ ⊆ O → A.SmoothOn (U ∩ O) h →
    A.SmoothOn U (O.indicator fun y => χ y * h y)

def NormSqSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X) (g : X → ℂ),
    A.HoloOn U g → A.SmoothOn U (fun y => ‖g y‖ ^ 2)

def BdWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (g : Fin R.n → Fin R.n → X → ℂ),
    (∀ j k, A.HoloOn (bdDom R j ∩ bdDom R k) (g j k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, g j k y ≠ 0) →
    (∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y) →
    ∃ w : Fin R.n → X → ℝ, (∀ j, A.SmoothOn (bdDom R j) (w j)) ∧
      (∀ j, ∀ y ∈ bdDom R j, 0 < w j y) ∧
      ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, w j y = ‖g j k y‖ ^ 2 * w k y

def BdMetric.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ φ : Fin R.n → X → ℝ, IsBdMetric R φ

def BddOnInner.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n)
    (u : X → ℝ), ContinuousOn u (bdDom R j) → ∃ B : ℝ, ∀ y ∈ R.V'' j, |u y| ≤ B

def BdSectionProps.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    IsPotential A (bdPot R φ c) ∧ IsSection A (bdPot R φ c) (bdSec R) ∧ secOpen (bdSec R) = R.Yo

def BdNormCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    Continuous fun y => ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)

def BdComparison.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec (bdPot R φ c) (bdSec R) y| ≤ B

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 holoOn_const)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
