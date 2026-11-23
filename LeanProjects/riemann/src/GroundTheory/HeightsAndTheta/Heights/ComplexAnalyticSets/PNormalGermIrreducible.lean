import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtensionLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusIdentity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem eq_zero_of_mem_closure_of_continuousAt {σ : Type} [Fintype σ] {k : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} {u : σ → ℂ} (hk : ContinuousAt k u) (hu : u ∈ closure S)
    (h0 : ∀ y ∈ S, k y = 0) : k u = 0 := by
  have h1 := hk.continuousWithinAt.mem_closure_image hu
  have h2 : k '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h0 y hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

theorem NormalGermIrreducible.proof (hreg : RegularLocusIdentity.Statement)
    (hext : NormalRiemannExtensionLocal.Statement) (hvan : VanishNearPoint.Statement) :
    NormalGermIrreducible.Statement := by
  classical
  intro σ _ I w hI hnorm hw
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  set X := zeroSetIn I with hX
  obtain ⟨h, hhI, hid⟩ := hreg σ I hI

  set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩
    {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds
  have hwU : w ∈ U := ⟨⟨hf, hg⟩, hfg⟩

  set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE

  have key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0)) := by
    rintro z ⟨hzX, hzU⟩ hhz
    obtain ⟨V, hVo, hzV, hVU, hVid⟩ := hid z hzX hhz U (hUo.mem_nhds hzU)
    refine ⟨V, hVo, hzV, hVU, ?_⟩
    have hfV : AnalyticOnNhd ℂ f V := fun y hy => (hVU hy).1.1
    have hgV : AnalyticOnNhd ℂ g V := fun y hy => (hVU hy).1.2
    by_cases hA : ∃ y ∈ X ∩ V, E y
    · left
      have hf0 := hVid f hfV hA
      intro u hu
      filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩
    · right
      push Not at hA
      have hnz : ¬ E z := hA z ⟨hzX, hzV⟩
      have hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0 := by
        rw [Filter.not_eventually] at hnz
        refine hnz.mono fun y hy => ?_
        by_contra hc
        exact hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩
      obtain ⟨y, ⟨hyX, hfy⟩, hyV⟩ := (hfr.and_eventually (hVo.mem_nhds hzV)).exists
      have hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0 := by
        filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX
        exact (mul_eq_zero.1 (hu huX)).resolve_left hfu
      have hg0V := hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩
      exact fun u hu => ⟨hA u hu, hg0V u hu⟩

  set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ
  set S := (X ∩ U) \ {z | eval z h = 0} with hS
  have hφhol : HolomorphicOnSubset φ S := by
    rintro z ⟨hzXU, hhz⟩
    obtain ⟨V, hVo, hzV, -, hcase⟩ := key z hzXU hhz
    refine ⟨V, hVo, hzV, ?_⟩
    rcases hcase with h0 | h1
    · refine ⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]
    · refine ⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]
  have hφb : Bornology.IsBounded (φ '' S) := by
    refine ((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_
    rintro _ ⟨z, -, rfl⟩
    by_cases hz : E z
    · simp [hφ, hz]
    · simp [hφ, hz]
  obtain ⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩ :=
    hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb

  set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN
  have hNo : IsOpen N := hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball
  have hwN : w ∈ N := ⟨hwV, Metric.mem_ball_self (by norm_num)⟩
  have hdense := zeroSetIn_subset_closure_diff hvan I h hI hhI

  have spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) →
      (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0 := by
    intro k hk h0
    filter_upwards [hNo.mem_nhds hwN] with u huN huX
    have hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0})) := hNo.inter_closure ⟨huN, hdense huX⟩
    exact eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl
      fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2
  have hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2 := by
    rintro y ⟨hyX, hyV, hyF⟩ hhy
    rw [← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]
    simpa [dist_eq_norm] using hyF
  by_cases hc : ‖F w‖ < 1 / 2
  · left
    refine spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_
    have hEy : E y := by
      by_contra hnE
      have h1 := hφN y hy hhy
      simp only [hφ, if_neg hnE] at h1
      have : ‖(1 : ℂ)‖ < 1 := by
        calc ‖(1 : ℂ)‖ = ‖(1 - F w) + F w‖ := by ring_nf
          _ ≤ ‖1 - F w‖ + ‖F w‖ := norm_add_le _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 hc
          _ = 1 := by norm_num
      simp at this
    exact hEy.self_of_nhds hy.1
  · right
    refine spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_
    have hnE : ¬ E y := by
      intro hEy
      have h1 := hφN y hy hhy
      simp only [hφ, if_pos hEy, zero_sub, norm_neg] at h1
      exact hc h1
    obtain ⟨V', -, hyV', -, hcase⟩ := key y ⟨hy.1, hVU hy.2.1⟩ hhy
    rcases hcase with h0 | h1
    · exact absurd (h0 y ⟨hy.1, hyV'⟩) hnE
    · exact (h1 y ⟨hy.1, hyV'⟩).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
