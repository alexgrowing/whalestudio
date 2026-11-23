import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyUniformModerateGrowth
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

theorem GlobalTheory.EisRes.laurentMul_locally_uniform_moderate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 (((n : ℂ) - 1) / 2) → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H s g = (s - (((n : ℂ) - 1) / 2)) ^ k * Eis s g) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∃ (C : ℝ) (N : ℕ), ∀ s ∈ V, ∀ g, ‖H s g‖ ≤ C * (height σ J g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c _hS hP k U H hU hH hHE
  obtain ⟨k₀, U₀, H₀, hU₀, hH₀E, hH₀sm, hH₀w⟩ := hP.2.2.2.1 (((n : ℂ) - 1) / 2)
  obtain ⟨V₀, hV₀, C₀, N₀, hB⟩ := GlobalTheory.WeakHolFamily.locally_uniform_moderate_growth F E σ n J H₀ _ U₀ hU₀ hH₀sm hH₀w
  have hW : U ∩ U₀ ∩ V₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) := inter_mem (inter_mem hU hU₀) hV₀
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.1 hW
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hr : (0:ℝ) < R / 2 := half_pos hR
  have hcb : Metric.closedBall ρ (R / 2) ⊆ U ∩ U₀ ∩ V₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRsub
  refine ⟨Metric.ball ρ (R / 2), Metric.ball_mem_nhds ρ hr, (R / 2) ^ k / (R / 2) ^ k₀ * C₀, N₀, ?_⟩
  intro s hs g
  have hd : DiffContOnCl ℂ (H · g) (Metric.ball ρ (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball ρ hr.ne']
    exact (hH g).mono (fun z hz => (hcb hz).1.1)
  have hfr : ∀ z ∈ frontier (Metric.ball ρ (R / 2)),
      ‖H z g‖ ≤ (R / 2) ^ k / (R / 2) ^ k₀ * C₀ * (height σ J g : ℝ) ^ N₀ := by
    intro z hz
    rw [frontier_ball ρ hr.ne'] at hz
    have hz' : dist z ρ = R / 2 := hz
    have hzc : z ∈ Metric.closedBall ρ (R / 2) := Metric.sphere_subset_closedBall hz
    obtain ⟨⟨hzU, hzU₀⟩, hzV₀⟩ := hcb hzc
    have hne : z ≠ ρ := by
      intro e
      rw [e, dist_self] at hz'
      linarith
    have h1 := hHE z hzU hne g
    have h2 := hH₀E z hzU₀ hne g
    have hn : ‖z - ρ‖ = R / 2 := by rw [← dist_eq_norm]; exact hz'
    have hb := hB z hzV₀ g
    rw [h2, norm_mul, norm_pow, hn] at hb
    rw [h1, norm_mul, norm_pow, hn]
    have hpos : 0 < (R / 2) ^ k₀ := pow_pos hr _
    have hq : 0 ≤ (R / 2) ^ k / (R / 2) ^ k₀ := div_nonneg (pow_pos hr _).le hpos.le
    calc (R / 2) ^ k * ‖Eis z g‖ = (R / 2) ^ k / (R / 2) ^ k₀ * ((R / 2) ^ k₀ * ‖Eis z g‖) := by
          field_simp
      _ ≤ (R / 2) ^ k / (R / 2) ^ k₀ * (C₀ * (height σ J g : ℝ) ^ N₀) := mul_le_mul_of_nonneg_left hb hq
      _ = (R / 2) ^ k / (R / 2) ^ k₀ * C₀ * (height σ J g : ℝ) ^ N₀ := by ring
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hfr (subset_closure hs)

end
