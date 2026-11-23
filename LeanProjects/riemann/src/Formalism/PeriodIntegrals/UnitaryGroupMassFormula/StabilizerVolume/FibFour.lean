import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibOfTens

noncomputable section

namespace PI.VolStabS

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
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν := by
  constructor
  · intro h φ hφ; exact h φ hφ.1 hφ.2.1 hφ.2.2
  · intro h φ h1 h2 h3; exact h φ ⟨h1, h2, h3⟩

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

theorem densOn_of [T2Space X] [OpensMeasurableSpace X] {P : (V → ℝ) → Prop} {μ : Measure V}
    {f : V → Y} {ι : X → Y} {χ : Y → X → ℂ} {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
    (h1 : NSPhase P μ f χ ν) (h2 : InvDens P μ f ι χ ν) : DensOn P μ f ι ν := by
  intro φ hφ
  obtain ⟨hc, hS⟩ := h2 φ hφ (h1 φ hφ)
  refine ⟨fun b => (invT μ f ι χ ν φ b).re, Complex.continuous_re.comp hc, fun S hSc => ?_⟩
  have e := hS S hSc
  have hi : IntegrableOn (invT μ f ι χ ν φ) S ν := hc.continuousOn.integrableOn_compact hSc
  have h3 : ∫ b in S, (invT μ f ι χ ν φ b).re ∂ν = (∫ b in S, invT μ f ι χ ν φ b ∂ν).re :=
    integral_re hi
  rw [h3, ← e, integral_complex_ofReal, Complex.ofReal_re]

theorem densAll_of_four [T2Space X] [OpensMeasurableSpace X] {P : (V → ℝ) → Prop}
    {μ : Measure V} {f : V → Y} {ι : X → Y} {χ : Y → X → ℂ} {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] {U : Set V} (h1 : NSPhase P μ f χ ν) (h2 : InvDens P μ f ι χ ν)
    (h3 : DensApprox P μ f ι ν U) : DensAll μ f ι ν U :=
  (densAll_iff μ f ι ν U).2 (h3 (densOn_of h1 h2))

end Four

end PI.VolStabS
