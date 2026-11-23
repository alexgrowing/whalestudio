import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic

namespace DifferentiableLines

open Metric Filter Topology Set Complex
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic

open scoped Real

theorem differentiableAt_of_lines {k : ℕ} {U O : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hO : IsOpen O) (hg : DifferentiableOn ℂ g U) (hgO : ∀ t ∈ U, g t ≠ 0 → t ∈ O)
    (hf : DifferentiableOn ℂ f O)
    (hl : ∀ τ ∈ U, τ ∉ O → ∀ v : Fin k → ℂ, (∀ᶠ z : ℂ in 𝓝[≠] 0, τ + z • v ∈ O) →
      Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] 0) (𝓝 (f τ)))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) (hne : ∀ r > 0, ∃ t ∈ ball τ₀ r, g t ≠ 0) : DifferentiableAt ℂ f τ₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU τ₀ hτ₀
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne (r / 2) (by linarith)
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
  have hga : ∀ τ ∈ ball τ₀ (r / 4), AnalyticOnNhd ℂ (fun z : ℂ => g (τ + z • v)) (ball 0 (3 / 2)) := by
    intro τ hτ
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have h1 : DifferentiableAt ℂ g (τ + z • v) :=
      hg.differentiableAt (hU.mem_nhds (hline τ hτ z (mem_ball_zero_iff.mp hz)))
    exact (h1.comp z (hlined τ z)).differentiableWithinAt
  have hiso : ∀ τ ∈ ball τ₀ (r / 4), ∀ z₁ ∈ ball (0 : ℂ) (3 / 2), g (τ + z₁ • v) ≠ 0 →
      ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), ∀ᶠ z in 𝓝[≠] z₀, g (τ + z • v) ≠ 0 := fun τ hτ z₁ hz₁ h z₀ hz₀ =>
    (hga τ hτ z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h' =>
      h ((hga τ hτ).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hz₀ h' hz₁)
  have hτ₀b : τ₀ ∈ ball τ₀ (r / 4) := mem_ball_self (by linarith)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := mem_ball_self (by norm_num)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball_zero_iff]
    norm_num
  obtain ⟨ε, hε, hεφ⟩ : ∃ ε > 0, ∀ z : ℂ, dist z 0 < ε → z ≠ 0 → g (τ₀ + z • v) ≠ 0 :=
    Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp
      (hiso τ₀ hτ₀b 1 h1 (by simpa [hvdef] using hgt₁) 0 h0))
  set ρ : ℝ := min ε 1 / 2 with hρdef
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε 1
    linarith
  have hρ1 : ρ < 3 / 2 := by
    have := min_le_right ε 1
    linarith
  have hO' : IsOpen (U ∩ {t | g t ≠ 0}) := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
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
    exact hPc.continuousAt.preimage_mem_nhds (hO'.mem_nhds (hsph₀ z hz))
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
  have hdiff := differentiableOn_circleAverage hO hf hρ.le fun τ hτ z hz => hgO _ (hK τ hτ z hz).1 (hK τ hτ z hz).2
  refine (((hdiff.const_mul I).const_mul (2 * π * I : ℂ)⁻¹).differentiableAt (ball_mem_nhds τ₀ hδ)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds τ₀ hδ] with τ hτ
  have hτr := hδr hτ
  have hρs : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ := by simp [abs_of_pos hρ]
  have hρb : (ρ : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by simpa [abs_of_pos hρ] using hρ1
  have hin : ∀ z, τ + z • v ∈ O → DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z := fun z hz =>
    (hf.differentiableAt (hO.mem_nhds hz)).comp z (hlined τ z)
  have hH : ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z₀ := by
    intro z₀ hz₀
    by_cases hz : τ + z₀ • v ∈ O
    · exact hin z₀ hz
    have e₁ : ∀ᶠ z in 𝓝[≠] z₀, τ + z • v ∈ O := by
      filter_upwards [hiso τ hτr ρ hρb (hK τ (ball_subset_closedBall hτ) ρ hρs).2 z₀ hz₀,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz₀)] with z h h'
      exact hgO _ (hline τ hτr z (mem_ball_zero_iff.mp h')) h
    have t₁ : Tendsto (fun w : ℂ => z₀ + w) (𝓝[≠] 0) (𝓝[≠] z₀) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((continuous_add_left z₀).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa using hw⟩
    have t₂ : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((continuous_sub_right z₀).tendsto z₀).mono_left (nhdsWithin_le_nhds (s := {z₀}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa [sub_eq_zero] using hw⟩
    have e₂ := hl _ (hline τ hτr z₀ (mem_ball_zero_iff.mp hz₀)) hz v
      ((t₁.eventually e₁).mono fun w hw => by rwa [add_smul, ← add_assoc] at hw)
    have e₃ : Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] z₀) (𝓝 (f (τ + z₀ • v))) :=
      (e₂.comp t₂).congr fun z => by simp only [Function.comp_apply, add_assoc, ← add_smul, add_sub_cancel]
    exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt (e₁.mono hin)
      (continuousAt_iff_punctured_nhds.2 e₃)).differentiableAt
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 (3 / 2) := closedBall_subset_ball hρ1
  have hC := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) countable_empty (mem_ball_self hρ)
    (fun z hz => (hH z (hcl hz)).continuousAt.continuousWithinAt)
    (fun z hz => hH z (hcl (ball_subset_closedBall hz.1)))
  simp only [sub_zero, zero_smul, add_zero] at hC
  rw [circleIntegral_inv_smul_eq hρ.ne' (fun z => f (τ + z • v)), smul_eq_mul] at hC
  exact hC.symm

end DifferentiableLines
