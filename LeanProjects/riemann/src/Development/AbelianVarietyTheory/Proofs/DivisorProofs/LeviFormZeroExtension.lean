import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory

theorem levi_eq_zero_of_eq_off_coord_hyperplane :
    ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (r : ℝ) (f g : (Fin e → ℂ) → ℝ), ContDiffOn ℝ ∞ g {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → g z = f z) → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → ∀ w, levi f z w = 0) → ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → ∀ w, levi g z w = 0 := by
  intro e S i c r f g hg hgf hf z hz hzS w
  set V : Set (Fin e → ℂ) := {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} with hVdef
  have hVo : IsOpen V := by
    have hV : V = Metric.ball c r ∩ ⋂ k ∈ S, {z : Fin e → ℂ | z k ≠ 0} := by
      ext x; simp [V]
    rw [hV]
    exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
      isOpen_ne_fun (continuous_apply k) continuous_const)
  have hzero : ∀ y ∈ V, y i ≠ 0 → levi g y w = 0 := by
    intro y hy hyi
    have hmem : V ∩ {x : Fin e → ℂ | x i ≠ 0} ∈ 𝓝 y :=
      (hVo.inter (isOpen_ne_fun (continuous_apply i) continuous_const)).mem_nhds ⟨hy, hyi⟩
    have hev : g =ᶠ[𝓝 y] f := by
      filter_upwards [hmem] with x hx using hgf x hx.1.1 hx.1.2 hx.2
    rw [levi_congr hev]
    exact hf y hy.1 hy.2 hyi w
  have hzV : z ∈ V := ⟨hz, hzS⟩
  by_cases hzi : z i ≠ 0
  · exact hzero z hzV hzi
  push_neg at hzi
  have hg2 : ContDiffOn ℝ 2 g V := hg.of_le (by norm_cast)
  have hcont : ContinuousOn (fun y => levi g y w) V := by
    have h1 := continuousOn_levi hVo hg2
    have hpr : ContinuousOn (fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ))) V :=
      (continuous_id.prodMk continuous_const).continuousOn
    have h3 := ContinuousOn.comp (f := fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ)))
      h1 hpr (fun x hx => ⟨hx, Set.mem_univ _⟩)
    exact h3
  set A : Set (Fin e → ℂ) := V ∩ {x | x i ≠ 0} with hAdef
  let p : ℝ → (Fin e → ℂ) := fun t => z + (t : ℂ) • Pi.single i 1
  have hp : Tendsto p (𝓝[≠] 0) (𝓝 z) := by
    have hpc : Continuous p := by fun_prop
    have h0 := hpc.tendsto 0
    have hp0 : p 0 = z := by simp [p]
    rw [hp0] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hpA : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ A := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ V := hp.eventually (hVo.mem_nhds hzV)
    have h2 : ∀ᶠ t in 𝓝[≠] (0:ℝ), t ≠ 0 := self_mem_nhdsWithin
    filter_upwards [h1, h2] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    simp [p, hzi, ht2]
  have hcl : z ∈ closure A := mem_closure_of_tendsto hp hpA
  haveI : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hT : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 (levi g z w)) :=
    ((hcont z hzV).mono inter_subset_left).tendsto
  have hT0 : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hzero y hy.1 hy.2).symm
  exact tendsto_nhds_unique hT hT0

end GlobalTheory
