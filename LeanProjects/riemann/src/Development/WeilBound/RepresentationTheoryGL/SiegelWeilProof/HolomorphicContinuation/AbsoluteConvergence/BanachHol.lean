import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

def BanachHol : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  ∃ Φ : ℂ → C(X, ℂ), DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, ∀ x, Φ z x = F z x

def DslopeFam : Prop := ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] (U : Set ℂ) (s₀ : ℂ) (F : ℂ → X → ℂ),
  IsOpen U → s₀ ∈ U → ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  (∀ x, F s₀ x = 0) →
  ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ univ) ∧
    ∀ x, DifferentiableOn ℂ (fun z => dslope (fun z => F z x) s₀ z) U

def FactorL : Prop := ∀ (G : Type) [TopologicalSpace G] (S : Submodule ℂ (G → ℂ)) (l : (G → ℂ) → ℂ) (C : Set G),
  IsCompact C → (∀ F ∈ S, Continuous F) → (∀ (a : ℂ), ∀ F ∈ S, ∀ F' ∈ S, l (a • F + F') = a * l F + l F') →
  (∀ F ∈ S, ∀ M : ℝ, (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M) →
  ∃ L : C(C, ℂ) →L[ℂ] ℂ, ∀ F ∈ S, ∀ (hF : Continuous F), l F = L ⟨fun x => F x, hF.comp continuous_subtype_val⟩

def KRCpt : Prop := ∀ n : ℕ, CompactSpace (KR n)

end PositivityTheory.Rg.Sw.AbsSt
