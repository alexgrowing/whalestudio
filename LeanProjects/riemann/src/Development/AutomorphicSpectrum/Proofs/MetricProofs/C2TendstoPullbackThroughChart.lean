import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ChartPullBack

theorem comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  simp [Function.comp, c.right_inv hy]

theorem fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) z = fderiv ℝ f z :=
  (comp_symm_eventuallyEq c f hz).fderiv_eq

theorem fderiv_comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] fderiv ℝ f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  exact fderiv_comp_symm_eq c f hy

theorem fderiv_fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) :
    fderiv ℝ (fderiv ℝ ((f ∘ c) ∘ c.symm)) z = fderiv ℝ (fderiv ℝ f) z :=
  (fderiv_comp_symm_eventuallyEq c f hz).fderiv_eq

theorem C2_tendsto_chart_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  intro e X _ c g p K' hK h
  obtain ⟨h0, h1, h2, M, hM⟩ := h
  refine ⟨h0.congr (Eventually.of_forall fun t z hz => ?_),
    h1.congr (Eventually.of_forall fun t z hz => ?_),
    h2.congr (Eventually.of_forall fun t z hz => ?_),
    M, hM.mono fun t ht z hz => ?_⟩
  · exact ((comp_symm_eventuallyEq c (g t) (hK hz)).eq_of_nhds).symm
  · exact (fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · exact (fderiv_fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · rw [fderiv_comp_symm_eq c (g t) (hK hz)]
    exact ht z hz

end GlobalTheory.CompanionTheory.Metric.ChartPullBack
