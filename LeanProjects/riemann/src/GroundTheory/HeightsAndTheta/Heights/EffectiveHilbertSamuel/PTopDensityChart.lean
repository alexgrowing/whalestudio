import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsTopDensityChart
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace TopDensityChartProof

variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem jac_mul_jac (A : FinHolAtlas D U) (j c : Fin A.n) {x : U}
    (hx : x ∈ (A.chart j).source ∩ (A.chart c).source) : jac A j c x * jac A c j x = 1 := by
  have hσ : DifferentiableAt ℂ (A.chart j ∘ (A.chart c).symm) (A.chart c x) :=
    (A.holo c j (A.chart c x) ⟨(A.chart c).map_source hx.2, by
      simp [(A.chart c).left_inv hx.2, hx.1]⟩).differentiableAt
  have hσx : (A.chart j ∘ (A.chart c).symm) (A.chart c x) = A.chart j x := by
    simp [(A.chart c).left_inv hx.2]
  have hτ : DifferentiableAt ℂ (A.chart c ∘ (A.chart j).symm)
      ((A.chart j ∘ (A.chart c).symm) (A.chart c x)) := by
    rw [hσx]
    exact (A.holo j c (A.chart j x) ⟨(A.chart j).map_source hx.1, by
      simp [(A.chart j).left_inv hx.1, hx.2]⟩).differentiableAt
  have heq : (A.chart c ∘ (A.chart j).symm) ∘ (A.chart j ∘ (A.chart c).symm) =ᶠ[𝓝 (A.chart c x)]
      id := by
    have hopen := (A.chart c).isOpen_inter_preimage_symm (A.chart j).open_source
    filter_upwards [hopen.mem_nhds ⟨(A.chart c).map_source hx.2, by
      simp [(A.chart c).left_inv hx.2, hx.1]⟩] with y hy
    simp [(A.chart j).left_inv hy.2, (A.chart c).right_inv hy.1]
  have h1 := fderiv_comp (A.chart c x) hτ hσ
  rw [heq.fderiv_eq, fderiv_id, hσx] at h1
  have h2 := congrArg (fun f : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) =>
    LinearMap.det (f : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) h1
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at h2
  unfold jac
  rw [← LinearMap.det_comp]
  exact h2.symm

end TopDensityChartProof

open TopDensityChartProof in

theorem TopDensityChart.proof : TopDensityChart.Statement := by
  intro D U _ A L₂ L m ψ G hψ hG c B _ hB
  let s : Fin A.n → Set (Fin D → ℂ) := fun j =>
    piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart c).source)
  let τ : Fin A.n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => A.chart c ∘ (A.chart j).symm
  have hcover : B ⊆ ⋃ j, τ j '' s j := by
    intro y hy
    have hyc := hB hy
    have hxc : (A.chart c).symm y ∈ (A.chart c).source := (A.chart c).map_target hyc
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min wellFounded_lt
      {k | (A.chart c).symm y ∈ (A.chart k).source} ⟨c, hxc⟩
    refine mem_iUnion.2 ⟨j, A.chart j ((A.chart c).symm y),
      ⟨⟨(A.chart j).map_source hj, fun k hk => ?_⟩, (A.chart j).map_source hj, ?_⟩, ?_⟩
    · rw [(A.chart j).left_inv hj]
      exact fun h => hmin k h hk
    · simp [(A.chart j).left_inv hj, hxc]
    · simp [τ, (A.chart j).left_inv hj, (A.chart c).right_inv hyc]
  calc _ ≤ ∫⁻ y in ⋃ j, τ j '' s j, ENNReal.ofReal (2 ^ D * ‖G c ((A.chart c).symm y)‖ ^ 2 *
          Real.exp (-ψ c ((A.chart c).symm y))) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ y in τ j '' s j, ENNReal.ofReal (2 ^ D * ‖G c ((A.chart c).symm y)‖ ^ 2 *
          Real.exp (-ψ c ((A.chart c).symm y))) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ y in τ j '' s j, ENNReal.ofReal (2 ^ D * ‖G c ((A.chart c).symm y)‖ ^ 2 *
          Real.exp (-ψ c ((A.chart c).symm y))) := tsum_fintype _
    _ ≤ ∑ j, ∫⁻ y in piece A j, ENNReal.ofReal (2 ^ D * ‖G j ((A.chart j).symm y)‖ ^ 2 *
          Real.exp (-ψ j ((A.chart j).symm y))) := Finset.sum_le_sum fun j _ => ?_
    _ = topNormSq A ψ G := rfl
  have hsm : MeasurableSet (s j) := (ExtensionProof.measurableSet_piece A j).inter
    ((A.chart j).isOpen_inter_preimage_symm (A.chart c).open_source).measurableSet
  have hder : ∀ z ∈ s j, HasFDerivWithinAt (τ j)
      ((fderiv ℂ (τ j) z).restrictScalars ℝ) (s j) z := fun z hz =>
    ((A.holo j c z hz.2).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : InjOn (τ j) (s j) := by
    intro z₁ h₁ z₂ h₂ he
    have := (A.chart c).injOn h₁.2.2 h₂.2.2 he
    rw [← (A.chart j).right_inv h₁.2.1, ← (A.chart j).right_inv h₂.2.1, this]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hder hinj]
  refine le_trans (le_of_eq (setLIntegral_congr_fun hsm fun z hz => ?_))
    (lintegral_mono_set inter_subset_left)
  obtain ⟨x, hxj, rfl⟩ : ∃ x ∈ (A.chart j).source, A.chart j x = z :=
    ⟨_, (A.chart j).map_target hz.2.1, (A.chart j).right_inv hz.2.1⟩
  have hxc : x ∈ (A.chart c).source := by simpa [(A.chart j).left_inv hxj] using hz.2.2
  have hτx : (A.chart c).symm (τ j (A.chart j x)) = x := by
    simp [τ, (A.chart j).left_inv hxj, (A.chart c).left_inv hxc]
  have hdet : ((fderiv ℂ (τ j) (A.chart j x)).restrictScalars ℝ :
      (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)).det = ‖jac A j c x‖ ^ 2 := by
    change LinearMap.det (((fderiv ℂ (τ j) (A.chart j x) :
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
    rfl
  have hjj := jac_mul_jac A j c ⟨hxj, hxc⟩
  have hab : ‖jac A j c x‖ * ‖jac A c j x‖ = 1 := by rw [← norm_mul, hjj, norm_one]
  have hh : 0 < ‖L₂.g c j x * L.g c j x ^ m‖ := norm_pos_iff.2
    (mul_ne_zero (L₂.ne_zero c j x ⟨hxc, hxj⟩) (pow_ne_zero _ (L.ne_zero c j x ⟨hxc, hxj⟩)))
  have hGn : ‖G c x‖ = ‖jac A c j x‖ * ‖L₂.g c j x * L.g c j x ^ m‖ * ‖G j x‖ := by
    rw [hG c j x ⟨hxc, hxj⟩]
    simp only [norm_mul, norm_pow]
    ring
  have hex : Real.exp (-ψ c x) = Real.exp (-ψ j x) * (‖L₂.g c j x * L.g c j x ^ m‖ ^ 2)⁻¹ := by
    rw [hψ c j x ⟨hxc, hxj⟩, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log (by positivity)]
  rw [hτx, hdet, (A.chart j).left_inv hxj, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_nonneg (sq_nonneg _), hGn, hex]
  have hh2 : ‖L₂.g c j x * L.g c j x ^ m‖ ^ 2 ≠ 0 := by positivity
  field_simp
  linear_combination ‖G j x‖ ^ 2 * (‖jac A j c x‖ * ‖jac A c j x‖ + 1) * hab

end

end GroundTheory.Heights₂.Heights.EffectiveHS
