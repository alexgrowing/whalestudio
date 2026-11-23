import GroundTheory.AutomorphicForms.TraceClass

open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] {ι : Type*} {b : ι → H}
    (hb : Orthonormal ℂ b) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2)) ?_
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.2 (by norm_num))
  intro i j hij
  refine Metric.ball_disjoint_ball ?_
  have h0 : ⟪b i, b j⟫_ℂ = 0 := hb.2 hij
  have h := norm_sub_sq (𝕜 := ℂ) (b i) (b j)
  rw [h0, hb.1 i, hb.1 j] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (b i - b j)]

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {E : Type*} [NormedAddCommGroup E] (f : X → E) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem UpperTheory.ConvolutionTheory.K.hsOfKer :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
      (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k : X → Lp ℂ 2 ν), MemLp k 2 ν →
      (∀ φ, (A φ : X → ℂ) =ᵐ[ν] fun x => ⟪k x, φ⟫_ℂ) → IsHilbertSchmidt A := by
  intro X _ ν _ _ A k hk hA
  let b := stdHilbertBasis ℂ (Lp ℂ 2 ν)
  haveI := UpperTheory.ConvolutionTheory.K.hsOfKer_countable b.orthonormal
  rw [isHilbertSchmidt_iff b]
  have h1 : ∀ i, ‖A (b i)‖ₑ ^ 2 = ∫⁻ x, ‖⟪b i, k x⟫_ℂ‖ₑ ^ 2 ∂ν := by
    intro i
    rw [Lp.enorm_def, eLpNorm_congr_ae (hA (b i)), UpperTheory.ConvolutionTheory.K.hsOfKer_sq]
    simp only [enorm_inner_comm (k _)]
  simp only [h1]
  rw [← lintegral_tsum]
  · simp only [← enorm_sq_eq_tsum b]
    rw [← UpperTheory.ConvolutionTheory.K.hsOfKer_sq]
    exact ENNReal.pow_lt_top hk.2
  · intro i
    exact ((aestronglyMeasurable_const.inner hk.1).enorm).pow_const 2
