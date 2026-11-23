import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloEtaleIffChartsStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  intro n Y _ _ _ _ _ ι La _ A la U z β F0 hE hβ hF
  have hfun : (fun y : U => GlobalTheory.OTY.TwEst.ext0 U F0 y) = F0 :=
    funext fun y => GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U F0 y
  have hd := (GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale n Y ι La A U z hE (GlobalTheory.OTY.TwEst.ext0 U F0)).1 (by rw [hfun]; exact hF)
  refine ⟨⟨fun i => (hβ.1.1 i).mul (hd i), fun i j y hy hi hj => ?_⟩, ?_⟩
  · show β i y * _ = _ * (β j y * _)
    rw [hβ.1.2 i j y hy hi hj, mul_assoc]
  · have hc : ContinuousOn (GlobalTheory.OTY.TwEst.ext0 U F0) U := by
      intro y hy
      have hs := A.mem_pick y
      set e := A.chart (A.pick y) with he
      have hop : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hE.isOpen
      have hm : e y ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hs, by simpa [e.left_inv hs] using hy⟩
      have h1 : ContinuousAt (GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) (e y) :=
        (hd (A.pick y)).continuousOn.continuousAt (hop.mem_nhds hm)
      have h2 : ContinuousAt ((GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) ∘ e) y :=
        h1.comp (e.continuousAt hs)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with x hx
      simp [e.left_inv hx]
    classical
    have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)) (s := Uᶜ))
      hE.isOpen.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, GlobalTheory.OTY.TwEst.ext0]
