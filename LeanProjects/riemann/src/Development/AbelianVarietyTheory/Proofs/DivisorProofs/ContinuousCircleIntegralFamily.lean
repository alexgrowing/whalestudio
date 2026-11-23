import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleCont

theorem continuous_circleIntegral_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    Continuous fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  intro F E _ _ _ _ _ σ hσ n J hJ H₀ s₀ r V hV hr hsub hH hμ j
  have hsph : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  obtain ⟨-, N, C, hC⟩ := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
    (isCompact_sphere s₀ r) hsph hH hμ [] (by simp)
  have hhol : ∀ g, DifferentiableOn ℂ (fun s => H₀ s g) V := fun g =>
    (hμ _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).congr fun s _ => rfl
  have hcm : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  rw [continuous_iff_continuousAt]
  intro g₀
  unfold circleIntegral
  have hne : ∀ θ, circleMap s₀ r θ - s₀ ≠ 0 := fun θ => sub_ne_zero.2 (circleMap_ne_center hr.ne')
  have hn1 : ∀ θ, ‖circleMap s₀ r θ - s₀‖ = r := fun θ => by rw [← dist_eq_norm]; exact hcm θ
  have hev : ∀ᶠ g in 𝓝 g₀, (height σ J g : ℝ) < height σ J g₀ + 1 :=
    hht.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  simp_rw [deriv_circleMap]
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => r * (r ^ j * (|C| * ((height σ J g₀ : ℝ) + 1) ^ N))) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun g => Continuous.aestronglyMeasurable ?_
    exact ((continuous_circleMap 0 r).mul continuous_const).smul
      ((((continuous_circleMap s₀ r).sub continuous_const).zpow₀ j (fun θ => Or.inl (hne θ))).mul
        ((hhol g).continuousOn.comp_continuous (continuous_circleMap s₀ r) (fun θ => hsph (hcm θ))))
  · filter_upwards [hev] with g hg
    refine ae_of_all _ fun θ _ => ?_
    rw [← circleMap_sub_center, norm_smul, norm_mul, norm_mul, norm_zpow, hn1, Complex.norm_I, mul_one]
    have h0 : (0 : ℝ) ≤ (height σ J g : ℝ) := NNReal.coe_nonneg _
    have h1 : ‖H₀ (circleMap s₀ r θ) g‖ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
      calc ‖H₀ (circleMap s₀ r θ) g‖ ≤ C * (height σ J g : ℝ) ^ N := hC _ (hcm θ) g
        _ ≤ |C| * (height σ J g : ℝ) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hg.le N) (abs_nonneg C)
    have h2 : (0 : ℝ) < r ^ j := zpow_pos hr j
    gcongr
  · refine ae_of_all _ fun θ _ => ?_
    exact ((continuous_const.mul (hH _ (hsph (hcm θ))).cont).const_smul (circleMap 0 r θ * Complex.I)).continuousAt
end GlobalTheory.CircleCont
