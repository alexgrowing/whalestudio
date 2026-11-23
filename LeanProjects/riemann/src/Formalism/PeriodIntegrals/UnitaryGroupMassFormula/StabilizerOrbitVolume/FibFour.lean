import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibOfTens

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

section Four

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

def DensOn (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) : Prop :=
  ∀ φ : V → ℝ, P φ → ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def IsCcOn (U : Set V) (φ : V → ℝ) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

theorem densAll_iff (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν :=
  ⟨fun h φ hφ => h φ hφ.1 hφ.2.1 hφ.2.2, fun h φ h1 h2 h3 => h φ ⟨h1, h2, h3⟩⟩

def fourT (μ : Measure V) (f : V → Y) (χ : Y → X → ℂ) (φ : V → ℝ) (S : X) : ℂ :=
  ∫ v, (φ v : ℂ) * χ (f v) S ∂μ

def invT (μ : Measure V) (f : V → Y) (ι : X → Y) (χ : Y → X → ℂ) (ν : Measure X) (φ : V → ℝ)
    (b : X) : ℂ :=
  ∫ S, fourT μ f χ φ S * starRingEnd ℂ (χ (ι b) S) ∂ν

def NSPhase (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (χ : Y → X → ℂ) (ν : Measure X) :
    Prop :=
  ∀ φ, P φ → Integrable (fourT μ f χ φ) ν

def InvDens (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (χ : Y → X → ℂ)
    (ν : Measure X) : Prop :=
  ∀ φ, P φ → Integrable (fourT μ f χ φ) ν →
    Continuous (invT μ f ι χ ν φ) ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), (φ v : ℂ) ∂μ = ∫ b in S, invT μ f ι χ ν φ b ∂ν

def DensApprox (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  DensOn P μ f ι ν → DensOn (IsCcOn U) μ f ι ν

end Four

end PI.VolStabSW
