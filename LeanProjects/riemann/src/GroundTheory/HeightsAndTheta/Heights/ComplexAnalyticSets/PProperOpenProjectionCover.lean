import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionBranchLocus
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem subset_closure_nonvanishing_of_open {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by
  obtain ⟨y₁, hy₁D, hy₁⟩ := hne
  intro x hx
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hempty
  have hzero : δ =ᶠ[𝓝 (A x)] 0 := by
    filter_upwards [hopen x hx V hV] with y hy
    obtain ⟨x', ⟨hx'Y, hx'V⟩, rfl⟩ := hy
    by_contra h0
    exact hempty ⟨x', hx'V, hx'Y, h0⟩
  exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hmaps hx) hzero hy₁D)

theorem ProperOpenProjectionCover.proof (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
