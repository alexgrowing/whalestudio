import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam

namespace GlobalTheory.ShFam

theorem IsDivNorm.exists_ball_lipschitz {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : AnRead p σ d} {C : TopologicalSpace.Closeds Y} {n : CxPts p σ → ℝ} (h : IsDivNorm R C n)
    (c : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ ε > 0, ∃ (g : ReciprocityTheory.L2DbarEstimates.V d → ℂ) (F : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (A : ℝ), 0 ≤ A ∧
      ∀ w ∈ Metric.ball (c.e y) ε, w ∈ c.e.target ∧ n (c.e.symm w) ^ 2 = ‖g w‖ ^ 2 * Real.exp (-F w) ∧
        |F w| ≤ A ∧ ∀ w' ∈ Metric.ball (c.e y) ε, ‖g w - g w'‖ ≤ A * ‖w - w'‖ := by
  obtain ⟨V, t, f, hV, -, hf, e⟩ := h.2 y
  have hS := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) V.1)
  have hn := hS.mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hy hV)
  have hg := ((GlobalTheory.ChartGlue.contDiffOn_real hS (c.holo V.1 t)).contDiffAt hn).of_le
    (m := 1) (by exact_mod_cast le_top)
  obtain ⟨K, T, hT, hK⟩ := hg.exists_lipschitzOnWith
  have hF : ContinuousAt (f ∘ c.e.symm) (c.e y) :=
    ((hf.chart (isOpen_ptsIn _) c).continuousOn).continuousAt hn
  have hB : ∀ᶠ w in nhds (c.e y), |(f ∘ c.e.symm) w| < |(f ∘ c.e.symm) (c.e y)| + 1 :=
    hF.abs.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hn (Filter.inter_mem hT hB))
  refine ⟨ε, hε, ev p σ V.1 t ∘ c.e.symm, f ∘ c.e.symm, max K (|(f ∘ c.e.symm) (c.e y)| + 1),
    le_max_of_le_left K.2, fun w hw => ⟨(hb hw).1.1, e _ (hb hw).1.2,
      le_max_of_le_right (le_of_lt (hb hw).2.2), fun w' hw' => ?_⟩⟩
  have := hK.dist_le_mul w (hb hw).2.1 w' (hb hw').2.1
  rw [dist_eq_norm, dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end GlobalTheory.ShFam
