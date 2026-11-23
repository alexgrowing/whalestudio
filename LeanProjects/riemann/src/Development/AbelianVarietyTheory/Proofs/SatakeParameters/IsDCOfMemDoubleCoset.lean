import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight

namespace GlobalTheory.HkB

open Formalism.IndefR.Bridge

theorem isDC_of_mem_doubleCoset {G : Type} [Group G] {J : Subgroup G} {x x' : G} {A : Finset G}
    (hA : IsDC J x' A) (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) : IsDC J x A := by
  obtain ⟨k₁, k₂, rfl⟩ := hx
  constructor
  · intro a ha
    obtain ⟨u, v, rfl⟩ := hA.1 a ha
    exact ⟨u * k₁, k₂ * v, by simp [mul_assoc]⟩
  · rintro _ ⟨u, v, rfl⟩
    exact hA.2 _ ⟨u * k₁⁻¹, k₂⁻¹ * v, by simp [mul_assoc]⟩

theorem dcOp_eq_and_level {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J L : Subgroup G) (χ : J →* ℂˣ) (x x' : G) (A A' : Finset G) (F : G → W)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) (hAL : ∀ a ∈ A, a ∈ L) (hAL' : ∀ a ∈ A', a ∈ L)
    (hA : IsDC J x A) (hA' : IsDC J x' A') (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂)
    (hF : ∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) :
    dcOp A F = dcOp A' F ∧ (∀ (k : J) (h : G), (dcOp A F) (h * k) = (χ k : ℂ) • (dcOp A F) h) := by
  have hF' : F ∈ AdForms (1 : G →* G) (1 : G →* Module.End ℂ W) J χ := by
    intro γ h k
    simpa using hF k h
  refine ⟨dcOp_eq_of_isDC _ _ hχ hA (isDC_of_mem_doubleCoset hA' hx) hAL hAL' hF', fun k h => ?_⟩
  have h1 := LocSplit.dcOp_mem (1 : G →* G) (1 : G →* Module.End ℂ W) hs hχ hA hAL hF' 1 h k
  simpa using h1

end GlobalTheory.HkB
