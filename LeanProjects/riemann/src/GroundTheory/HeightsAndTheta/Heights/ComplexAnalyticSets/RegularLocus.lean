import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsRegularPointOf {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (x : σ → ℂ) : Prop :=
  x ∈ Y ∧ ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
    (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O

def regLocus {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {x | IsRegularPointOf Y x}

theorem regLocus_subset {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : regLocus Y ⊆ Y :=
  fun _ hx => hx.1

theorem isRegularPointOf_regLocus {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {x : σ → ℂ}
    (hx : x ∈ regLocus Y) : IsRegularPointOf (regLocus Y) x := by
  have hx' : IsRegularPointOf Y x := hx
  obtain ⟨hxY, d, A, O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hx'
  refine ⟨hx, d, A, O, V, g, hO, hV, hxV, hg, hAg, ?_⟩
  rw [← hYV]
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨regLocus_subset Y hz, hzV⟩
  · rintro ⟨hzY, hzV⟩
    exact ⟨⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩, hzV⟩

def seqWithLimit : Set (Fin 1 → ℂ) :=
  insert 0 (Set.range fun n : ℕ => fun _ : Fin 1 => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
