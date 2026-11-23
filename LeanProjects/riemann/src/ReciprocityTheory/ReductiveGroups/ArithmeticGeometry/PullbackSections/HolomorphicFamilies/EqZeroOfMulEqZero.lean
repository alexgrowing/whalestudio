import Mathlib
import Lemmata.FirstBlockLemmaJ.Imports

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open Metric Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eq_zero_on_ball {g : V → ℂ} {x : V} {ε : ℝ} (hg : DifferentiableOn ℂ g (ball x ε)) {z : V}
    (hz : z ∈ ball x ε) (hgz : g =ᶠ[𝓝 z] 0) : ∀ y ∈ ball x ε, g y = 0 := by
  first | exact Bl.FirstBlockLemmaJ.goal1 .. | (apply Bl.FirstBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaJ.goal1 <;> assumption)

theorem eq_zero_of_eventually {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {g : V → ℂ}
    (hg : DifferentiableOn ℂ g U) {x0 : V} (hx0 : x0 ∈ U) (h0 : g =ᶠ[𝓝 x0] 0) : ∀ y ∈ U, g y = 0 := by
  have hZo : IsOpen {x : V | g =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {x : V | g =ᶠ[𝓝 x] 0} := by
    refine hc.subset_of_closure_inter_subset hZo ⟨x0, hx0, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hzb : z ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hzd
    have hall := eq_zero_on_ball (hg.mono hb) hzb hzZ
    exact Filter.eventually_of_mem (ball_mem_nhds x hε) hall
  intro y hy
  exact (hsub hy).self_of_nhds

theorem eq_zero_of_mul_eq_zero {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by
  refine eq_zero_of_eventually hU hc hg hx0 ?_
  have h1 : ∀ᶠ y in 𝓝 x0, f y ≠ 0 := (hf.continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne h0
  filter_upwards [h1, hU.mem_nhds hx0] with y hy hyU
  exact (mul_eq_zero.mp (hfg y hyU)).resolve_left hy

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
