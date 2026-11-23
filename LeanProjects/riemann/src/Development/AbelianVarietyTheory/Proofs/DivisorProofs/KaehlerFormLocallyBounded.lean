import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam

open scoped ContDiff
set_option autoImplicit false

namespace GlobalTheory.ShFam

open ReciprocityTheory.L2DbarEstimates in

theorem continuousAt_wd_wdb {d : ℕ} {g : V d → ℂ} {v : V d} (hg : ContDiffAt ℝ 2 g v) (j k : Fin d) :
    ContinuousAt (fun w => wd d j (wdb d k g) w) v := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) v := hg.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (wdb d k g) v := by
    unfold wdb
    exact (((h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul
      (h1.clm_apply contDiffAt_const))).div_const _)
  have h3 : ContDiffAt ℝ 0 (fderiv ℝ (wdb d k g)) v := h2.fderiv_right (by norm_num)
  have h4 := h3.continuousAt
  unfold wd
  exact (((h4.clm_apply continuousAt_const).sub (continuousAt_const.mul
    (h4.clm_apply continuousAt_const))).div_const _)

theorem IsKaehlerForm.bound_ball {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : AnRead p σ d} {a : ChartForm p σ d} (h : IsKaehlerForm R a) (c : AlgChart p σ d) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : ∃ ε > 0, ∃ B : ℝ, ∀ w ∈ Metric.ball (c.e y) ε, w ∈ c.e.target ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c (c.e.symm w) ξ.ofLp ≤ B * ‖ξ‖ ^ 2 := by
  obtain ⟨W, φ, hyW, hWo, hs, e⟩ := h.1 y
  set O := c.e.target ∩ c.e.symm ⁻¹' W with hO
  have hOo : IsOpen O := GlobalTheory.ChartGlue.isOpen_over c.e hWo
  have hv : c.e y ∈ O := GlobalTheory.ChartGlue.mem_over c.e hy hyW
  have hc : ContDiffOn ℝ ∞ (φ ∘ c.e.symm) O := hs.chart hWo c
  set g : ReciprocityTheory.L2DbarEstimates.V d → ℂ := fun v => ((φ (c.e.symm v) : ℝ) : ℂ) with hg
  have hgc : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hc
  have hg2 : ContDiffAt ℝ 2 g (c.e y) := (hgc.contDiffAt (hOo.mem_nhds hv)).of_le ENat.LEInfty.out
  set N : ReciprocityTheory.L2DbarEstimates.V d → ℝ := fun w => ∑ j, ∑ k, ‖ReciprocityTheory.L2DbarEstimates.wd d j (ReciprocityTheory.L2DbarEstimates.wdb d k g) w‖ with hN
  have hNc : ContinuousAt N (c.e y) :=
    tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun k _ =>
      (continuousAt_wd_wdb hg2 j k).norm
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousAt_iff.1 hNc 1 one_pos
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 hOo _ hv
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (N (c.e y) + 1) / Real.pi, fun w hw => ?_⟩
  have hw₁ : dist w (c.e y) < δ₁ := lt_of_lt_of_le hw (min_le_left _ _)
  have hwO : w ∈ O := hb₂ (lt_of_lt_of_le (Metric.mem_ball.1 hw) (min_le_right _ _))
  refine ⟨hwO.1, fun ξ => ?_⟩
  have hN1 : N w ≤ N (c.e y) + 1 := by
    have := hb₁ hw₁
    rw [Real.dist_eq] at this
    linarith [le_abs_self (N w - N (c.e y))]
  have hsrc : c.e.symm w ∈ c.e.source := c.e.map_target hwO.1
  rw [e c _ hsrc hwO.2, ddcForm, AlgChart.levi, c.e.right_inv hwO.1]
  have hL : (ReciprocityTheory.L2DbarEstimates.leviV d (fun v => ((φ (c.e.symm v) : ℝ) : ℂ)) w ξ.ofLp).re ≤ N w * ‖ξ‖ ^ 2 := by
    refine (Complex.re_le_norm _).trans ?_
    unfold ReciprocityTheory.L2DbarEstimates.leviV
    refine (norm_sum_le _ _).trans ?_
    rw [hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, mul_assoc, sq]
    have hj := PiLp.norm_apply_le ξ j
    have hk := PiLp.norm_apply_le ξ k
    exact mul_le_mul_of_nonneg_left (mul_le_mul hj hk (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right (hL.trans ?_) Real.pi_pos.le
  exact mul_le_mul_of_nonneg_right hN1 (sq_nonneg _)

end GlobalTheory.ShFam
