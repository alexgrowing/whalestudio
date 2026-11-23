import Mathlib

open Filter Topology

namespace EisTube

variable {ι : Type}

def reV (z : ι → ℂ) : ι → ℝ := fun i => (z i).re

def imV (z : ι → ℂ) : ι → ℝ := fun i => (z i).im

def tube (Ω : Set (ι → ℝ)) : Set (ι → ℂ) := {z | reV z ∈ Ω}

def farCone {J : Type*} [Fintype ι] (a : J → ι → ℝ) (R : ℝ) : Set (ι → ℝ) :=
  {x | ∀ j, R < ∑ i, x i * a j i}

def TubeExtends [Fintype ι] (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] : Prop :=
  ∀ (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
  (∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂) →
  ∀ (h : P → ℝ), (∀ p, 0 ≤ h p) → (∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) →
  ∀ (F : (ι → ℂ) → P → ℂ),
  (∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) →
  (∀ z ∈ tube Ω, Continuous (F z)) →
  (∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) →
  ∃ G : (ι → ℂ) → P → ℂ,
    (∀ p, Differentiable ℂ (fun z => G z p)) ∧
    (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
    Continuous (Function.uncurry G) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p)

end EisTube
