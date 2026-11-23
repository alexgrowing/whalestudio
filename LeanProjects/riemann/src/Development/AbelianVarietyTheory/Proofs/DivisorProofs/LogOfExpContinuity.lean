import Mathlib

open Filter Topology Set

namespace GlobalTheory

theorem pathLog_variation_continuousAt :
    ∀ (B : Type) [TopologicalSpace B] (b₀ : B) (V : Set B) (a : B × ℝ → ℂ), V ∈ nhds b₀ →
      ContinuousOn (fun q => Complex.exp (a q)) (V ×ˢ Set.Icc (0 : ℝ) 1) →
      (∀ b ∈ V, ContinuousOn (fun x : ℝ => a (b, x)) (Set.Icc 0 1)) →
      ContinuousAt (fun b => a (b, 1) - a (b, 0)) b₀ := by
  intro B _ b₀ V a hV hE ha
  have hb₀ : b₀ ∈ V := mem_of_mem_nhds hV
  let F : B × unitInterval → ℂ := fun z => Complex.exp (a (z.1, (z.2 : ℝ)))
  have hF : ∀ x : unitInterval, ContinuousAt F (b₀, x) := by
    intro x
    have h1 : ContinuousWithinAt (fun q => Complex.exp (a q)) (V ×ˢ Set.Icc (0 : ℝ) 1)
        (b₀, (x : ℝ)) := hE _ ⟨hb₀, x.2⟩
    have h2 : ContinuousAt (fun z : B × unitInterval => (z.1, (z.2 : ℝ))) (b₀, x) := by fun_prop
    have h3 : ∀ᶠ z : B × unitInterval in 𝓝 (b₀, x),
        (z.1, (z.2 : ℝ)) ∈ V ×ˢ Set.Icc (0 : ℝ) 1 := by
      have h4 : ∀ᶠ z : B × unitInterval in 𝓝 (b₀, x), z.1 ∈ V :=
        continuous_fst.continuousAt.eventually_mem hV
      filter_upwards [h4] with z hz using ⟨hz, z.2.2⟩
    exact h1.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h2, h3⟩)
  let Q : B → unitInterval → ℂ := fun b x => F (b, x) / F (b₀, x)
  have hQ1 : ∀ x, Q b₀ x = 1 := fun x => div_self (Complex.exp_ne_zero _)
  have hQc : ∀ x : unitInterval,
      ContinuousAt (fun z : B × unitInterval => Q z.1 z.2) (b₀, x) := by
    intro x
    have hden : ContinuousAt (fun z : B × unitInterval => F (b₀, z.2)) (b₀, x) :=
      ContinuousAt.comp (f := fun z : B × unitInterval => (b₀, z.2)) (g := F) (hF x)
        (by fun_prop)
    exact ContinuousAt.div (hF x) hden (Complex.exp_ne_zero _)
  have hev : ∀ᶠ b in 𝓝 b₀, ∀ x ∈ (univ : Set unitInterval), Q b x ∈ Metric.ball (1 : ℂ) 1 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ => ?_
    have hb : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (Q b₀ x) := by
      rw [hQ1]; exact Metric.ball_mem_nhds _ one_pos
    exact (hQc x).eventually_mem hb
  have hab : ∀ b' ∈ V, Continuous (fun x : unitInterval => a (b', (x : ℝ))) :=
    fun b' h => continuousOn_iff_continuous_restrict.1 (ha b' h)
  have hFc : ∀ b' ∈ V, Continuous fun x : unitInterval => F (b', x) :=
    fun b' h => Complex.continuous_exp.comp (hab b' h)
  have hid : ∀ᶠ b in 𝓝 b₀, (a (b₀, 1) - a (b₀, 0)) + Complex.log (Q b 1) - Complex.log (Q b 0)
      = a (b, 1) - a (b, 0) := by
    filter_upwards [hev, hV] with b hb hbV
    have hslit : ∀ x, Q b x ∈ Complex.slitPlane :=
      fun x => Complex.ball_one_subset_slitPlane (hb x (mem_univ _))
    let g : unitInterval → ℂ := fun x => a (b, x) - a (b₀, x) - Complex.log (Q b x)
    have hQcont : Continuous (Q b) :=
      (hFc b hbV).div (hFc b₀ hb₀) (fun _ => Complex.exp_ne_zero _)
    have hg : Continuous g :=
      ((hab b hbV).sub (hab b₀ hb₀)).sub (hQcont.clog hslit)
    have hexp : ∀ x, Complex.exp (g x) = 1 := by
      intro x
      have hQ0 : Q b x ≠ 0 := Complex.slitPlane_ne_zero (hslit x)
      have e1 : Complex.exp (a (b, x) - a (b₀, x)) = Q b x := Complex.exp_sub _ _
      simp only [g]
      rw [Complex.exp_sub, e1, Complex.exp_log hQ0, div_self hQ0]
    have hconst : g 1 = g 0 :=
      Complex.isCoveringMap_exp.const_of_comp hg
        (fun y y' => Subtype.ext ((hexp y).trans (hexp y').symm)) 1 0
    have hg10 : a (b, 1) - a (b₀, 1) - Complex.log (Q b 1)
        = a (b, 0) - a (b₀, 0) - Complex.log (Q b 0) := hconst
    linear_combination -hg10
  have hq : ∀ k : unitInterval, ContinuousAt (fun b => Q b k) b₀ := fun k =>
    ContinuousAt.comp (f := fun b => (b, k)) (g := fun z : B × unitInterval => Q z.1 z.2)
      (hQc k) (by fun_prop)
  have hl : ∀ k, ContinuousAt (fun b => Complex.log (Q b k)) b₀ := fun k =>
    (hq k).clog (by rw [hQ1]; exact Complex.one_mem_slitPlane)
  exact ((continuousAt_const.add (hl 1)).sub (hl 0)).congr hid

end GlobalTheory
