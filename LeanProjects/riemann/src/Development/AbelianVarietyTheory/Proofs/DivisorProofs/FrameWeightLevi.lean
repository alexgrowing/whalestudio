import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas

theorem frameWeight_levi : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  intro n Y _ _ _ _ _ ι La _ A E U β J hU hβ hJ x hx i hi
  have hne : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s → ∀ y ∈ U,
      y ∈ (A.chart i).source → s i y ≠ 0 := by
    intro la s hs y hyU hyi
    rw [hs.1.2 i (A.pick y) y hyU hyi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne _ _ _ y hyi (A.mem_pick y)) (hs.2 y hyU)
  have hloc : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y))) =ᶠ[𝓝 x]
      fun y => A.ph E i y + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
    filter_upwards [(A.chart i).open_source.mem_nhds hi, hU.mem_nhds hx] with y hyi hyU
    have hp := A.mem_pick y
    have hb := hne _ β hβ y hyU hyi
    have hj := hne _ J hJ y hyU hyi
    have e1 := hyq_nsq_chart A (A.kap + E) β i y hyi (hβ.1.2 i _ y hyU hyi hp)
    have e2 := hyq_nsq_chart A A.kap J i y hyi (hJ.1.2 i _ y hyU hyi hp)
    have hb2 : 0 < ‖β i y‖ ^ 2 := by positivity
    have hj2 : 0 < ‖J i y‖ ^ 2 := by positivity
    rw [e1, e2, A.ph_add A.kap E i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
      Real.log_mul hb2.ne' (Real.exp_pos _).ne', Real.log_mul hj2.ne' (Real.exp_pos _).ne',
      Real.log_mul hj2.ne' (inv_pos.mpr hb2).ne', Real.log_inv, Real.log_exp, Real.log_exp]
    ring
  have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hU
  have hxW : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hholo : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s →
      ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (s i ∘ (A.chart i).symm) v := by
    intro la s hs
    filter_upwards [hWo.mem_nhds hxW] with v hv
    exact (hs.1.1 i v hv).differentiableAt (hWo.mem_nhds hv)
  have hevW : ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    hWo.mem_nhds hxW
  have hqd : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hholo _ β hβ, hholo _ J hJ, hevW] with v h1 h2 h3
    have hb := hne _ β hβ _ h3.2 ((A.chart i).map_target h3.1)
    exact h2.mul (h1.inv hb)
  have hq : ContDiffAt ℝ ∞ ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) :=
    hyq_contDiffAt_of_ev hqd
  have hqne : ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simp only [Function.comp, hc]
    exact mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))
  have hlog : ContDiffAt ℝ ∞ ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) :=
    (hq.norm_sq ℝ).log (by positivity)
  have hphE : ContDiffAt ℝ ∞ (A.ph E i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph E i).contDiffAt hT
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := ((A.chart i).continuousAt_symm ((A.chart i).map_source hi)).tendsto
    rwa [hc] at this
  refine ⟨?_, fun f hf ξ => ?_⟩
  · refine (hphE.add hlog).congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hloc] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  · have hloc' : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y)
        =ᶠ[𝓝 x] fun y => (A.ph E i y + f y) + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
      filter_upwards [hloc] with y hy
      rw [hy]; ring
    have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph E i y + f y) ∘ (A.chart i).symm) (A.chart i x) :=
      (hphE.add hf).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
        (A.chart i x) := hlog.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [leviAt_congr A i _ _ x hi hloc' ξ,
      leviAt_add A i (fun y => A.ph E i y + f y)
        (fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
      leviAt_log_normSq A i (fun y => J i y * (β i y)⁻¹) x hi hqd
        (mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))) ξ, add_zero]

end GlobalTheory
