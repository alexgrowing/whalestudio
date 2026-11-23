import GroundTheory.AutomorphicForms.TraceClass
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable

open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

private theorem lintegral_sq_ne_top {X H : Type} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup H] {u : X → H} (hu : MemLp u 2 ν) : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hu.2
  simpa using h.ne

private theorem parseval_integral {X H ι : Type} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (b : HilbertBasis ι ℂ H) {u v : X → H} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    ∑' i, ∫ x, ⟪u x, b i⟫_ℂ * ⟪b i, v x⟫_ℂ ∂ν = ∫ x, ⟪u x, v x⟫_ℂ ∂ν := by
  have hm : ∀ i, AEStronglyMeasurable (fun x => ⟪u x, b i⟫_ℂ * ⟪b i, v x⟫_ℂ) ν := fun i =>
    (hu.1.inner aestronglyMeasurable_const).mul (aestronglyMeasurable_const.inner hv.1)
  rw [← integral_tsum hm]
  · simp only [b.tsum_inner_mul_inner]
  · rw [← lintegral_tsum fun i => (hm i).enorm]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, (‖u x‖ₑ ^ 2 + ‖v x‖ₑ ^ 2) ∂ν) ?_ (lintegral_mono fun x => ?_)
    · rw [lintegral_add_left' (hu.1.enorm.pow_const 2)]
      exact ENNReal.add_ne_top.2 ⟨lintegral_sq_ne_top hu, lintegral_sq_ne_top hv⟩
    · rw [enorm_sq_eq_tsum b (u x), enorm_sq_eq_tsum b (v x), ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun i => ?_
      rw [enorm_mul, enorm_inner_comm (u x)]
      exact ennreal_mul_le_sq_add_sq _ _

theorem UpperTheory.ConvolutionTheory.K.traceKer :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
      (A M B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k₁ k₂ : X → Lp ℂ 2 ν), MemLp k₁ 2 ν → MemLp k₂ 2 ν →
      IsHilbertSchmidt A → IsHilbertSchmidt B →
      (∀ φ, (A φ : X → ℂ) =ᵐ[ν] fun x => ⟪k₁ x, φ⟫_ℂ) →
      (∀ φ, (ContinuousLinearMap.adjoint B φ : X → ℂ) =ᵐ[ν] fun x => ⟪k₂ x, φ⟫_ℂ) →
      trace (A ∘L M ∘L B) = ∫ x, ⟪k₁ x, M (k₂ x)⟫_ℂ ∂ν := by
  intro X _ ν _ _ A M B k₁ k₂ h₁ h₂ hA hB eA eB
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  have : Countable w := Formalism.MainNotions.LeviCoordinates.rrd_countable b.orthonormal
  have hMB : IsHilbertSchmidt (M ∘L B) := hB.comp_left M
  have h0 : trace (A ∘L M ∘L B) = ∑' i, ⟪b i, (M ∘L B) (A (b i))⟫_ℂ :=
    (hasSum_inner_comp_comm (stdHilbertBasis ℂ (Lp ℂ 2 ν)) b hA hMB).tsum_eq
  rw [h0, ← parseval_integral b (v := fun x => M (k₂ x)) h₁ (M.comp_memLp' h₂)]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left M, ← ContinuousLinearMap.adjoint_inner_left B,
    L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [eA (b i), eB (ContinuousLinearMap.adjoint M (b i))] with x hx hy
  rw [hx, hy, RCLike.inner_apply, inner_conj_symm, ContinuousLinearMap.adjoint_inner_left]
