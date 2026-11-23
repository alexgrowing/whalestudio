import Mathlib

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSA

theorem iteratedDeriv_ofReal' {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {h : ℝ → ℂ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hFh : ∀ x : ℝ, F x = h x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧ ∀ x : ℝ, iteratedDeriv p F x = iteratedDeriv p h x := by
  induction p with
  | zero => simpa using ⟨hF, hFh⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y) (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = iteratedDeriv p h := funext he
      rw [h4] at h3
      exact h3.deriv.symm

theorem eq_of_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h : ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0) (t : ℝ) : f t = g t := by
  have h0U : (0 : ℂ) ∈ U := by simpa using hmem 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hnear : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball), ← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball)]
    simp_rw [h]
  set V := connectedComponentIn U (0 : ℂ)
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have h0V : (0 : ℂ) ∈ V := mem_connectedComponentIn h0U
  have hRV : range (fun x : ℝ => (x : ℂ)) ⊆ V := by
    apply (isPreconnected_range Complex.continuous_ofReal).subset_connectedComponentIn
    · exact ⟨0, by simp⟩
    · rintro _ ⟨x, rfl⟩; exact hmem x
  have hVU : V ⊆ U := connectedComponentIn_subset _ _
  have hfa : AnalyticOnNhd ℂ f V := (hf.mono hVU).analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := (hg.mono hVU).analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc h0V hnear (hRV ⟨t, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt.TSA
