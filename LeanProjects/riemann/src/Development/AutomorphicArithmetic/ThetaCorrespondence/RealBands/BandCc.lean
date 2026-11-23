import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology Pointwise

theorem UpperTheory.Lit.Cusp.isBand_of_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ →
        IsBand N H (fun g => ∫ m, ψ (g * m) ∂ν) ∧ ∀ g, Integrable (fun m => ψ (g * m)) ν := by
  intro G _ _ _ _ _ _ _ _ N a H ν _ hN hinv hray ψ hψ hc
  have hint : ∀ g, Integrable (fun m => ψ (g * m)) ν := fun g =>
    (hψ.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.mulLeft g))
  have hcont : Continuous (fun g => ∫ m, ψ (g * m) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds g₀
    have hk : IsCompact (U⁻¹ * tsupport ψ) := hU.inv.mul hc
    have h := continuousOn_integral_of_compact_support (μ := ν) (f := fun g m => ψ (g * m)) (s := U) hk
      (hψ.comp (continuous_fst.mul continuous_snd)).continuousOn (fun p x hp hx => by
        by_contra hne
        exact hx ⟨p⁻¹, Set.inv_mem_inv.2 hp, p * x, subset_tsupport ψ hne, by simp⟩)
    exact h.continuousAt hUn
  have hI : ∀ g, ∀ m ∈ N, (∫ x, ψ (g * m * x) ∂ν) = ∫ x, ψ (g * x) ∂ν := by
    intro g m hm
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.mulLeft m) (fun x => ψ (g * x))
    have h2 : ν.map (MeasurableEquiv.mulLeft m) = ν := hinv m hm
    rw [h2] at h
    rw [h]
    simp [mul_assoc]
  have hex : ∀ g, (∫ m, ψ (g * m) ∂ν) ≠ 0 → ∃ m ∈ N, g * m ∈ tsupport ψ := by
    intro g hg
    by_contra hne
    apply hg
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ m ∂ν, m ∈ N := hN
    filter_upwards [hae] with m hm
    by_contra h0
    exact hne ⟨m, hm, subset_tsupport ψ h0⟩
  refine ⟨⟨hcont, ?_, hI, ?_⟩, hint⟩
  · obtain ⟨C, hC⟩ := (IsCompact.image hc hcont.norm).bddAbove
    refine ⟨max C 0, fun g => ?_⟩
    by_cases hg : (∫ m, ψ (g * m) ∂ν) = 0
    · simp [hg]
    · obtain ⟨m, hm, hs⟩ := hex g hg
      have := hC ⟨g * m, hs, rfl⟩
      simp only [hI g m hm] at this
      exact this.trans (le_max_left _ _)
  · obtain ⟨R, hR⟩ := (IsCompact.image hc hray.contH.abs).bddAbove
    refine ⟨R, fun g hg => ?_⟩
    obtain ⟨m, hm, hs⟩ := hex g hg
    have := hR ⟨g * m, hs, rfl⟩
    simpa only [hray.inv g m hm] using this
