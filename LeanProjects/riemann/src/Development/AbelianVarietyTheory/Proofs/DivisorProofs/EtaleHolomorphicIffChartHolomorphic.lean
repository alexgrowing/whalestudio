import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverseStatement

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem holo_etale_iff_holo_chart : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE Ω u hΩ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  constructor
  · intro h i v hv
    obtain ⟨hvt, hvU, hvΩ⟩ := hv
    obtain ⟨e, hes, hez⟩ := hloc ⟨(A.chart i).symm v, hvU⟩
    have he : IsChart n (fun y : U => z y) e := fun w _ => by rw [hez]
    have hev : ∀ w : U, e w = z w := fun w => by rw [← hez]
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 e.open_source
    have hO : IsOpen (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω)) :=
      e.isOpen_inter_preimage_symm (hΩ.preimage continuous_subtype_val)
    have hmem : z ((A.chart i).symm v) ∈ e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω) := by
      have h1 := hev ⟨(A.chart i).symm v, hvU⟩
      simp only at h1
      rw [← h1]
      refine ⟨e.map_source hes, ?_⟩
      simp only [Set.mem_preimage]
      rw [e.left_inv hes]
      exact hvΩ
    have h1 : DifferentiableAt ℂ ((fun y : U => u y) ∘ e.symm) (z ((A.chart i).symm v)) :=
      (h e he _ hmem).differentiableAt (hO.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (z ∘ (A.chart i).symm) v :=
      (hE.holo i v ⟨hvt, hvU⟩).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm hE.isOpen).mem_nhds ⟨hvt, hvU⟩)
    have h3 := DifferentiableAt.comp v (g := (fun y : U => u y) ∘ e.symm)
      (f := z ∘ (A.chart i).symm) h1 h2
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    have hvW : (A.chart i).symm v ∈ W := by
      rw [← hWe] at hes
      exact hes
    filter_upwards [((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hW)).mem_nhds
      ⟨hvt, hvU, hvW⟩] with v' hv'
    have hs : (⟨(A.chart i).symm v', hv'.2.1⟩ : U) ∈ e.source := by
      rw [← hWe]
      exact hv'.2.2
    have h4 := hev ⟨(A.chart i).symm v', hv'.2.1⟩
    simp only at h4
    simp only [Function.comp]
    rw [← h4, e.left_inv hs]
  · intro h e he v hv
    obtain ⟨hvt, hvΩ⟩ := hv
    have hs := A.mem_pick (e.symm v : U)
    set i := A.pick (e.symm v : U)
    obtain ⟨hc, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he v hvt i hs
    have hmem : A.chart i (e.symm v : U) ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) := by
      refine ⟨(A.chart i).map_source hs, ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart i).left_inv hs]
      exact ⟨(e.symm v).2, hvΩ⟩
    have h1 : DifferentiableAt ℂ (u ∘ (A.chart i).symm) (A.chart i (e.symm v : U)) :=
      (h i _ hmem).differentiableAt
        (((A.chart i).isOpen_inter_preimage_symm (hE.isOpen.inter hΩ)).mem_nhds hmem)
    have h3 := DifferentiableAt.comp v (g := u ∘ (A.chart i).symm)
      (f := fun v' => A.chart i (e.symm v' : U)) h1 (hc.differentiableAt (by simp))
    refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hev] with v' hv'
    simp only [Function.comp]
    rw [(A.chart i).left_inv hv']

end GlobalTheory.OTY
