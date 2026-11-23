import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverseStatement

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  unfold LeviNonneg
  intro x ξ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  obtain ⟨e, he, hx⟩ := exists_chart n (fun y : U => z y) hloc x
  obtain ⟨i, hxi, hsm, hpos⟩ := hφ x.1 x.2
  have hzx : z x = e x := he hx
  have hv : e x ∈ e.target := e.map_source hx
  have hsx : e.symm (e x) = x := e.left_inv hx
  obtain ⟨hG, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he (e x) hv i (by rw [hsx]; exact hxi)
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  show 0 ≤ (leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (z x) ξ).re
  rw [hzx]

  have heq : (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) =ᶠ[𝓝 (e x)]
      (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (e.symm v' : Y)) := by
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply, (A.chart i).left_inv hv']
  have hcongr : leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (e x) ξ =
      leviV n ((fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘
        (fun v' => A.chart i (e.symm v' : Y))) (e x) ξ := by
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 2
    apply wd_congr
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact ReciprocityTheory.L2DbarEstimates.wdb_congr hy
  have hU : ContDiffAt ℝ 2 (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ))
      ((fun v' => A.chart i (e.symm v' : Y)) (e x)) := by
    simp only [hsx]
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ hsm).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hcongr, flA_leviV_comp hU (hG.of_le (WithTop.coe_le_coe.mpr le_top)) ξ]
  simp only [hsx]
  exact hpos _

end GlobalTheory.OTY
