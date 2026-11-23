import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchImageNhdOffCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchImageNhdOffCentre.proof (h₁ : CurveRegularOffCentre.Statement) :
    BranchImageNhdOffCentre.Statement := by
  intro n I q hdim
  obtain ⟨N, hN, hreg⟩ := h₁ n I q hdim
  refine ⟨N, hN, fun c x hx hxq => ?_⟩
  obtain ⟨⟨σ₀, hσ₀, rfl⟩, hxN⟩ := hx
  obtain ⟨A, O, V, g, -, hV, hxV, -, hAg, hZV⟩ := hreg (c.toFun σ₀) ⟨c.mapsTo hσ₀, hxN⟩ hxq

  let e : ℂ → Fin 1 → ℂ := fun τ _ => τ
  have he_diff : Differentiable ℂ e := differentiable_pi.2 fun _ => differentiable_id
  have he_inj : Function.Injective e := fun a b h => congrFun h 0
  have hσe : e (σ₀ 0) = σ₀ := funext fun i => by fin_cases i; rfl
  have hBe : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, e τ ∈ Metric.ball 0 c.radius := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    rwa [pi_norm_const]
  have ht₀ : σ₀ 0 ∈ Metric.ball (0 : ℂ) c.radius := by
    have h := hσ₀
    rw [← hσe, mem_ball_zero_iff, pi_norm_const] at h
    rwa [mem_ball_zero_iff]
  have hB : Metric.ball (0 : ℂ) c.radius ∈ 𝓝 (σ₀ 0) := Metric.isOpen_ball.mem_nhds ht₀
  let f : ℂ → Fin n → ℂ := fun τ => c.toFun (e τ)
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 c.radius) :=
    c.differentiableOn.comp he_diff.differentiableOn hBe
  have hfV : f ⁻¹' V ∈ 𝓝 (σ₀ 0) :=
    (hfd.continuousOn.continuousAt hB).preimage_mem_nhds (by
      show V ∈ 𝓝 (c.toFun (e (σ₀ 0)))
      rw [hσe]
      exact hV.mem_nhds hxV)
  let Δ : Set ℂ := Metric.ball 0 c.radius ∩ f ⁻¹' V
  have hΔ : Δ ∈ 𝓝 (σ₀ 0) := inter_mem hB hfV

  have hfg : ∀ τ ∈ Δ, f τ = g (A (f τ)) := by
    rintro τ ⟨hτB, hτV⟩
    have h : f τ ∈ zeroSet I ∩ V := ⟨c.mapsTo (hBe τ hτB), hτV⟩
    rw [hZV] at h
    obtain ⟨y, hy, hgy⟩ := h
    rw [← hgy, hAg y hy]
  let φ : ℂ → ℂ := fun τ => A (f τ)
  have hφ : AnalyticAt ℂ φ (σ₀ 0) := (A.differentiable.comp_differentiableOn hfd).analyticAt hB

  have hopen : φ '' Δ ∈ 𝓝 (φ (σ₀ 0)) := by
    rcases hφ.eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have hev : ∀ᶠ τ in 𝓝[≠] (σ₀ 0), (φ τ = φ (σ₀ 0) ∧ τ ∈ Δ) ∧ τ ≠ σ₀ 0 :=
        ((hconst.and hΔ).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨τ, ⟨hτφ, hτΔ⟩, hτne⟩ := hev.exists
      have h1 : f τ = f (σ₀ 0) := by
        calc f τ = g (φ τ) := hfg τ hτΔ
          _ = g (φ (σ₀ 0)) := by rw [hτφ]
          _ = f (σ₀ 0) := (hfg (σ₀ 0) (mem_of_mem_nhds hΔ)).symm
      exact hτne (he_inj (c.injOn (hBe τ hτΔ.1) (hBe _ ht₀) h1))
    · exact hle (Filter.image_mem_map hΔ)
  have hφx : φ (σ₀ 0) = A (c.toFun σ₀) := by
    show A (c.toFun (e (σ₀ 0))) = _
    rw [hσe]
  refine ⟨V ∩ A ⁻¹' (φ '' Δ), inter_mem (hV.mem_nhds hxV)
    (A.continuous.continuousAt.preimage_mem_nhds (hφx ▸ hopen)), ?_⟩
  rintro y ⟨hyZ, hyV, τ, hτΔ, hτy⟩
  have hy : y ∈ g '' O := hZV ▸ ⟨hyZ, hyV⟩
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨e τ, hBe τ hτΔ.1, ?_⟩
  calc c.toFun (e τ) = f τ := rfl
    _ = g (φ τ) := hfg τ hτΔ
    _ = g w := by rw [hτy, hAg w hw]

end GroundTheory.Heights₂.Heights
