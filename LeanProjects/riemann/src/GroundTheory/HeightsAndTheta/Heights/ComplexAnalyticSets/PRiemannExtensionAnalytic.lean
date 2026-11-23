import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Metric Filter Topology Set Complex MeasureTheory

open scoped Real

noncomputable section

namespace RiemannExtensionAnalytic

theorem analyticOnNhd_of_differentiableOn {k : ℕ} {O : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) : AnalyticOnNhd ℂ f O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hf.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ f (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hf.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem circleIntegral_inv_smul_eq {ρ : ℝ} (hρ : ρ ≠ 0) (h : ℂ → ℂ) :
    (∮ z in C(0, ρ), z⁻¹ • h z) = I * ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 ρ θ) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hc : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ
  simp only [deriv_circleMap, smul_eq_mul]
  rw [mul_comm _ I, mul_assoc, mul_inv_cancel_left₀ hc]

theorem differentiableOn_circleAverage {k : ℕ} {O : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {τ₀ v : Fin k → ℂ} {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ O) :
    DifferentiableOn ℂ (fun τ => ∫ θ in (0 : ℝ)..2 * π, f (τ + circleMap 0 ρ θ • v)) (ball τ₀ δ) := by
  have hcd : ContinuousOn (fderiv ℂ f) O :=
    ((analyticOnNhd_of_differentiableOn hO hf).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
  have hKc : IsCompact ((fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v) '' (closedBall τ₀ δ ×ˢ sphere (0 : ℂ) ρ)) :=
    ((isCompact_closedBall τ₀ δ).prod (isCompact_sphere 0 ρ)).image hPc
  have hKO : (fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v) '' (closedBall τ₀ δ ×ˢ sphere (0 : ℂ) ρ) ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hK p.1 hp.1 p.2 hp.2
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcd.mono hKO)
  have hmem : ∀ τ ∈ closedBall τ₀ δ, ∀ θ : ℝ, τ + circleMap 0 ρ θ • v ∈ O := fun τ hτ θ =>
    hK τ hτ _ (circleMap_mem_sphere 0 hρ θ)
  have hcont : ∀ τ ∈ closedBall τ₀ δ, Continuous fun θ : ℝ => f (τ + circleMap 0 ρ θ • v) :=
    fun τ hτ => hf.continuousOn.comp_continuous (by fun_prop) (hmem τ hτ)
  intro τ₁ hτ₁
  have hs : ball τ₀ δ ∈ 𝓝 τ₁ := isOpen_ball.mem_nhds hτ₁
  have hτ₁c : τ₁ ∈ closedBall τ₀ δ := ball_subset_closedBall hτ₁
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
    (b := 2 * π) (F := fun τ θ => f (τ + circleMap 0 ρ θ • v))
    (F' := fun τ θ => fderiv ℂ f (τ + circleMap 0 ρ θ • v)) (bound := fun _ => M) hs ?_ ?_ ?_ ?_ ?_
    ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hs] with τ hτ
    exact (hcont τ (ball_subset_closedBall hτ)).aestronglyMeasurable
  · exact (hcont τ₁ hτ₁c).intervalIntegrable _ _
  · exact (hcd.comp_continuous (by fun_prop) (hmem τ₁ hτ₁c)).aestronglyMeasurable
  · refine Eventually.of_forall fun θ _ τ hτ => hM _ ⟨(τ, circleMap 0 ρ θ),
      ⟨ball_subset_closedBall hτ, circleMap_mem_sphere 0 hρ θ⟩, rfl⟩
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ τ hτ => ?_
    have h1 : HasFDerivAt f (fderiv ℂ f (τ + circleMap 0 ρ θ • v)) (τ + circleMap 0 ρ θ • v) :=
      (hf.differentiableAt (hO.mem_nhds (hmem τ (ball_subset_closedBall hτ) θ))).hasFDerivAt
    have h2 := h1.comp τ ((hasFDerivAt_id τ).add_const (circleMap 0 ρ θ • v))
    simpa [Function.comp_def] using h2

theorem slice_cauchy {R ρ : ℝ} {ψ h : ℂ → ℂ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hψ : DifferentiableOn ℂ ψ (ball 0 R)) (hsph : ∀ z ∈ sphere (0 : ℂ) ρ, ψ z ≠ 0) (hψ0 : ψ 0 ≠ 0)
    (hh : ∀ z ∈ ball (0 : ℂ) R, ψ z ≠ 0 → DifferentiableAt ℂ h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R, ∃ N ∈ 𝓝 z, ∃ C, ∀ w ∈ N, w ∈ ball (0 : ℂ) R → ψ w ≠ 0 → ‖h w‖ ≤ C) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • h z) = h 0 := by
  classical
  have hψa : AnalyticOnNhd ℂ ψ (ball 0 R) := hψ.analyticOnNhd isOpen_ball
  have h0R : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (hρ.trans hρR)
  have hiso : ∀ z₀ ∈ ball (0 : ℂ) R, ∀ᶠ z in 𝓝[≠] z₀, ψ z ≠ 0 := by
    intro z₀ hz₀
    rcases (hψa z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h' | h'
    · exact absurd (hψa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 R).isPreconnected
        hz₀ h' h0R) hψ0
    · exact h'
  set H : ℂ → ℂ := fun z => if ψ z = 0 then limUnder (𝓝[≠] z) h else h z with hH
  have hHd : ∀ z₀ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ H z₀ := by
    intro z₀ hz₀
    by_cases hz : ψ z₀ = 0
    · obtain ⟨N, hN, C, hC⟩ := hb z₀ hz₀
      have hev : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → ψ z ≠ 0 := eventually_nhdsWithin_iff.mp (hiso z₀ hz₀)
      have hsn : N ∩ ball (0 : ℂ) R ∩ {z | z ≠ z₀ → ψ z ≠ 0} ∈ 𝓝 z₀ :=
        inter_mem (inter_mem hN (isOpen_ball.mem_nhds hz₀)) hev
      have hdiff : DifferentiableOn ℂ (Function.update h z₀ (limUnder (𝓝[≠] z₀) h))
          (N ∩ ball (0 : ℂ) R ∩ {z | z ≠ z₀ → ψ z ≠ 0}) := by
        refine Complex.differentiableOn_update_limUnder_of_bddAbove hsn ?_ ?_
        · intro z hz'
          exact (hh z hz'.1.1.2 (hz'.1.2 hz'.2)).differentiableWithinAt
        · refine ⟨C, ?_⟩
          rintro _ ⟨z, hz', rfl⟩
          exact hC z hz'.1.1.1 hz'.1.1.2 (hz'.1.2 hz'.2)
      have heq : H =ᶠ[𝓝 z₀] Function.update h z₀ (limUnder (𝓝[≠] z₀) h) := by
        filter_upwards [hev] with z hz'
        by_cases hzz : z = z₀
        · subst hzz
          simp [hH, hz]
        · simp [hH, hz' hzz, Function.update_of_ne hzz]
      exact (hdiff.differentiableAt hsn).congr_of_eventuallyEq heq
    · have hev : ∀ᶠ z in 𝓝 z₀, ψ z ≠ 0 := (hψa z₀ hz₀).continuousAt.eventually_ne hz
      have heq : H =ᶠ[𝓝 z₀] h := by
        filter_upwards [hev] with z hz'
        simp [hH, hz']
      exact (hh z₀ hz₀ hz).congr_of_eventuallyEq heq
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hC := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) countable_empty (mem_ball_self hρ)
    (fun z hz => (hHd z (hcl hz)).continuousAt.continuousWithinAt)
    (fun z hz => hHd z (hcl (ball_subset_closedBall hz.1)))
  have hH0 : H 0 = h 0 := by simp [hH, hψ0]
  rw [← hH0, ← hC]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  simp [hH, hsph z hz]

theorem local_extension {k : ℕ} {U : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hf : DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}))
    (hb : ∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0})))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) :
    ∃ W ∈ 𝓝 τ₀, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      ∀ τ ∈ W, τ ∈ U → g τ ≠ 0 → F τ = f τ := by
  have hO : IsOpen (U ∩ {t | g t ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  by_cases hg0 : g τ₀ ≠ 0
  · exact ⟨U ∩ {t | g t ≠ 0}, hO.mem_nhds ⟨hτ₀, hg0⟩, f, hf, fun _ _ _ _ => rfl⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU τ₀ hτ₀
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne (ball τ₀ (r / 2)) isOpen_ball
    ((ball_subset_ball (by linarith)).trans hrU) ⟨τ₀, mem_ball_self (by linarith)⟩
  set v : Fin k → ℂ := t₁ - τ₀ with hvdef
  have hv : ‖v‖ < r / 2 := by
    rw [hvdef, ← dist_eq_norm]
    exact ht₁
  have hline : ∀ τ ∈ ball τ₀ (r / 4), ∀ z : ℂ, ‖z‖ < 3 / 2 → τ + z • v ∈ U := by
    intro τ hτ z hz
    apply hrU
    rw [mem_ball, dist_eq_norm] at hτ ⊢
    have h1 : ‖τ + z • v - τ₀‖ ≤ ‖τ - τ₀‖ + ‖z‖ * ‖v‖ := by
      rw [← norm_smul]
      calc ‖τ + z • v - τ₀‖ = ‖(τ - τ₀) + z • v‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z‖ * ‖v‖ ≤ 3 / 2 * (r / 2) := mul_le_mul hz.le hv.le (norm_nonneg _) (by norm_num)
    linarith
  have hlined : ∀ (τ : Fin k → ℂ) (z : ℂ), DifferentiableAt ℂ (fun z : ℂ => τ + z • v) z := by
    intro τ z
    fun_prop
  have hgline : ∀ τ ∈ ball τ₀ (r / 4),
      DifferentiableOn ℂ (fun z : ℂ => g (τ + z • v)) (ball 0 (3 / 2)) := by
    intro τ hτ z hz
    have h1 : DifferentiableAt ℂ g (τ + z • v) :=
      hg.differentiableAt (hU.mem_nhds (hline τ hτ z (mem_ball_zero_iff.mp hz)))
    exact (h1.comp z (hlined τ z)).differentiableWithinAt
  have hτ₀b : τ₀ ∈ ball τ₀ (r / 4) := mem_ball_self (by linarith)
  have hφa : AnalyticOnNhd ℂ (fun z : ℂ => g (τ₀ + z • v)) (ball 0 (3 / 2)) :=
    (hgline τ₀ hτ₀b).analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := mem_ball_self (by norm_num)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball_zero_iff]
    norm_num
  obtain ⟨ε, hε, hεφ⟩ : ∃ ε > 0, ∀ z : ℂ, dist z 0 < ε → z ≠ 0 → g (τ₀ + z • v) ≠ 0 := by
    rcases (hφa 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hgt₁
      have := hφa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected h0 h h1
      simpa [hvdef] using this
    · exact Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  set ρ : ℝ := min ε 1 / 2 with hρdef
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε 1
    linarith
  have hρ1 : ρ < 3 / 2 := by
    have := min_le_right ε 1
    linarith
  have hsph₀ : ∀ z ∈ sphere (0 : ℂ) ρ, τ₀ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    intro z hz
    have hz' : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    refine ⟨hline τ₀ hτ₀b z (by linarith), hεφ z (by rw [dist_zero_right]; linarith) ?_⟩
    rintro rfl
    rw [norm_zero] at hz'
    linarith
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun z hz => ?_
    have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
    exact hPc.continuousAt.preimage_mem_nhds (hO.mem_nhds (hsph₀ z hz))
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (r / 8) with hδdef
  have hδ : 0 < δ := by positivity
  have hδcl : closedBall τ₀ δ ⊆ ball τ₀ δ₀ := closedBall_subset_ball (by
    have := min_le_left (δ₀ / 2) (r / 8)
    linarith)
  have hδr : ball τ₀ δ ⊆ ball τ₀ (r / 4) := ball_subset_ball (by
    have := min_le_right (δ₀ / 2) (r / 8)
    linarith)
  have hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} :=
    fun τ hτ => hδ₀K (hδcl hτ)
  refine ⟨ball τ₀ δ, ball_mem_nhds τ₀ hδ,
    fun τ => (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • f (τ + z • v)), ?_, ?_⟩
  · have hdiff := differentiableOn_circleAverage hO hf hρ.le hK
    refine DifferentiableOn.congr ((hdiff.const_mul I).const_mul (2 * π * I : ℂ)⁻¹) fun τ _ => ?_
    show (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • f (τ + z • v)) = _
    rw [circleIntegral_inv_smul_eq hρ.ne' (fun z => f (τ + z • v)), smul_eq_mul]
  · intro τ hτ _ hgτ
    have hτr := hδr hτ
    have hh : ∀ z ∈ ball (0 : ℂ) (3 / 2), g (τ + z • v) ≠ 0 →
        DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z := by
      intro z hz hgz
      have h1 : DifferentiableAt ℂ f (τ + z • v) :=
        hf.differentiableAt (hO.mem_nhds ⟨hline τ hτr z (mem_ball_zero_iff.mp hz), hgz⟩)
      exact h1.comp z (hlined τ z)
    have hbd : ∀ z ∈ ball (0 : ℂ) (3 / 2), ∃ N ∈ 𝓝 z, ∃ C, ∀ w ∈ N, w ∈ ball (0 : ℂ) (3 / 2) →
        g (τ + w • v) ≠ 0 → ‖f (τ + w • v)‖ ≤ C := by
      intro z hz
      obtain ⟨N, hN, hNb⟩ := hb _ (hline τ hτr z (mem_ball_zero_iff.mp hz))
      obtain ⟨C, hC⟩ := hNb.exists_norm_le
      exact ⟨(fun w : ℂ => τ + w • v) ⁻¹' N, (hlined τ z).continuousAt.preimage_mem_nhds hN, C,
        fun w hwN hw hgw => hC _ ⟨_, ⟨⟨hwN, hline τ hτr w (mem_ball_zero_iff.mp hw)⟩, hgw⟩, rfl⟩⟩
    have := slice_cauchy (R := 3 / 2) (ψ := fun z => g (τ + z • v)) (h := fun z => f (τ + z • v)) hρ hρ1
      (hgline τ hτr) (fun z hz => (hK τ (ball_subset_closedBall hτ) z hz).2) (by simpa using hgτ) hh hbd
    simpa using this

end RiemannExtensionAnalytic

open RiemannExtensionAnalytic in

theorem RiemannExtensionAnalytic.proof : RiemannExtensionAnalytic.Statement := by
  intro k U g f hU hg hne hf hb
  have hloc := fun τ (hτ : τ ∈ U) => local_extension hU hg hne hf hb hτ
  choose! W hW Fl hFl hFlf using hloc
  have hdense : ∀ τ ∈ U, (𝓝[U ∩ {t | g t ≠ 0}] τ).NeBot := by
    intro τ hτ
    rw [← mem_closure_iff_nhdsWithin_neBot, _root_.mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ht, hgt⟩ := hne (o ∩ U) (ho.inter hU) inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  set F : (Fin k → ℂ) → ℂ := fun τ => limUnder (𝓝[U ∩ {t | g t ≠ 0}] τ) f with hF
  have key : ∀ τ₀ ∈ U, ∀ᶠ τ in 𝓝 τ₀, F τ = Fl τ₀ τ := by
    intro τ₀ hτ₀
    filter_upwards [eventually_eventually_nhds.mpr (hW τ₀ hτ₀), hU.mem_nhds hτ₀] with τ hτW hτU
    have := hdense τ hτU
    have hc : ContinuousAt (Fl τ₀) τ := ((hFl τ₀ hτ₀).differentiableAt hτW).continuousAt
    refine Tendsto.limUnder_eq ?_
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hτW, self_mem_nhdsWithin] with t htW htO
    exact hFlf τ₀ hτ₀ t htW htO.1 htO.2
  refine ⟨F, fun τ₀ hτ₀ => ?_, fun τ hτ => ?_⟩
  · exact (((hFl τ₀ hτ₀).differentiableAt (hW τ₀ hτ₀)).congr_of_eventuallyEq
      (key τ₀ hτ₀)).differentiableWithinAt
  · rw [(key τ hτ.1).self_of_nhds]
    exact hFlf τ hτ.1 τ (mem_of_mem_nhds (hW τ hτ.1)) hτ.1 hτ.2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
